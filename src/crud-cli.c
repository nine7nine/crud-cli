/*
 * crud-cli — a notcurses front end for the Claude Code engine.  (v2)
 *
 * Drives the closed `claude` binary headless over the stream-json + control
 * protocol and renders the conversation flush-left (no forced indent/bullets),
 * reflowing on resize.  Engine is a black box behind a stable wire protocol.
 *
 *   engine flags (verified against v2.1.169):
 *     -p --verbose --input-format stream-json --output-format stream-json
 *     --include-partial-messages --permission-mode default
 *     --permission-prompt-tool stdio        <- routes permission asks to us
 *
 * v2 adds: markdown rendering (headers / **bold** / `code` / fenced blocks),
 * tool & diff rendering (Bash/Read/Write/Edit with +/- coloring), a multiline
 * input editor (cursor nav, history, multi-line paste), and slash / @file
 * autocomplete + "allow & don't ask again" permissions.
 *
 * Rendering model (lulo lesson): ONE std plane, full-erase + redraw every dirty
 * frame, single notcurses_render — structurally ghost-proof and resize-correct.
 * Redraw is driven by engine events too, not just keystrokes.
 *
 * Build: make    Run: ./crud-cli    Quit: Ctrl-C / Ctrl-D
 *   Env: CRUD_CLAUDE_BIN (engine path), CRUD_MODEL (e.g. haiku for cheap runs)
 */
#define _GNU_SOURCE
#include <notcurses/notcurses.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <locale.h>
#include <dirent.h>
#include <ctype.h>
#include <time.h>
#include <pthread.h>
#include <sys/prctl.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "json.h"

/* Resolve the engine via PATH by default (the stable `claude` launcher, which always points at the
   current version) — robust across updates and for a system-wide install. Override with CRUD_CLAUDE_BIN. */
static const char *DEFAULT_BIN = "claude";
static const char *INIT_ID = "crud-cli-init-1";
static const char *USAGE_URL = "https://api.anthropic.com/api/oauth/usage";

/* plan usage, fetched by a background thread; -1 = unknown */
static double g_u5 = -1, g_u7 = -1; static long g_u5r = 0, g_u7r = 0;

/* JSON scanners (j_str/j_num/j_obj/j_escape/j_unescape_dup) live in json.c — see json.h */

/* ============================================================= styles ==== */
typedef struct { uint32_t fg; uint32_t bg; bool has_bg; bool bold; bool ital; bool dim; } Sty;
static const Sty STY_DEF = { 0xd0d0d0, 0, false, false, false, false };

/* ---- semantic UI palette (reused across functions; one place to retheme) ---- */
#define COL_BRAND     0x7d9bff    /* sprite, footer keys, prompt "> ", header titles, marked-block header */
#define COL_OV_TITLE  0x9ab8ff    /* overlay (picker/menu) title */
#define COL_OV_BORDER 0x6f86b8    /* overlay border */
#define COL_OV_SELBG  0x2f5fb0    /* overlay selected-row background */
#define COL_OV_ITEM   0xc9d2e6    /* overlay unselected item text */
#define COL_OV_BG     0x1d2231    /* overlay panel background */
#define COL_SEP       0x39435a    /* horizontal separator rule */
#define COL_DIM       0x8a93a6    /* dim / muted description text */
#define COL_OK        0x87d787    /* ok / green (accept-edits, enter key, toast, idle) */
#define COL_WARN      0xe6c25a    /* warn / amber (busy, vim prompt, ctrl-r highlight) */
#define COL_HINT      0x6a6a72    /* footer hint-label gray */
#define COL_CODEBG    0x1c1c1c    /* fenced-code dark background */
static bool sty_eq(Sty a, Sty b) {
    return a.fg==b.fg && a.bg==b.bg && a.has_bg==b.has_bg &&
           a.bold==b.bold && a.ital==b.ital && a.dim==b.dim;
}

/* ============================================================== blocks ==== */
/* Tool/result blocks store text whose lines may start with a marker byte:
 *   0x01 header  0x02 add(+green)  0x03 del(-red)  0x04 dim/context  0x05 code  */
typedef enum { B_USER, B_ASSISTANT, B_THINKING, B_TOOL, B_RESULT, B_SYS } Bkind;
/* fwd: RLine is defined with the render line list below; blocks cache their wrapped form. */
typedef struct RLine RLine;
typedef struct {
    Bkind kind; char *t; size_t len, cap;
    bool queued;                                  /* a user msg typed while busy — shown pending until sent */
    unsigned ver;                                 /* content version: bumped on every append */
    /* cached wrapped output, valid when (cver,cW,climit) == (ver,W,limit); cW<0 ⇒ empty */
    int cver, cW, climit;
    RLine *crl; int ncrl, crlcap;                 /* wrapped lines (own their Run[] arrays) */
    char *carena; int carn, carcap;               /* text arena the lines' runs index into */
} Block;
static Block *g_blk; static size_t g_nblk, g_blkcap;
static int g_cur_asst = -1, g_cur_think = -1;

static int blk_new(Bkind k) {
    if (g_nblk == g_blkcap) { g_blkcap = g_blkcap?g_blkcap*2:64; g_blk = realloc(g_blk, g_blkcap*sizeof*g_blk); }
    g_blk[g_nblk] = (Block){ .kind = k };
    g_blk[g_nblk].cW = -1;                          /* force a wrap on first render */
    return (int)g_nblk++;
}
static void blk_raw(int i, const char *s, size_t n) {
    Block *b = &g_blk[i];
    if (b->len + n + 1 > b->cap) { while (b->len+n+1 > b->cap) b->cap = b->cap?b->cap*2:128; b->t = realloc(b->t, b->cap); }
    memcpy(b->t + b->len, s, n); b->len += n; b->t[b->len] = 0;
    b->ver++;                                       /* invalidate this block's wrap cache */
}
static void blk_str(int i, const char *s) { blk_raw(i, s, strlen(s)); }
/* append plain text whose JSON escapes we decode */
static void blk_unesc(int i, const char *s) { char *u = j_unescape_dup(s); blk_str(i, u); free(u); }
/* append text, splitting on \n and prefixing each emitted line with `mark` */
static void blk_marked(int i, const char *plain, char mark) {
    const char *p = plain;
    while (*p) {
        const char *nl = strchr(p, '\n'); size_t L = nl ? (size_t)(nl-p) : strlen(p);
        char m = mark; blk_raw(i, &m, 1); blk_raw(i, p, L); blk_raw(i, "\n", 1);
        if (!nl) break;
        p = nl + 1;
    }
    if (p == plain) { char m = mark; blk_raw(i, &m, 1); blk_raw(i, "\n", 1); }
}
/* one diff line: marker + fixed 7-char prefix ("%4d " number + 2-char gutter) + code text.
   emit_marked colors the number dim, the gutter by marker, and highlights the code. */
static void emit_dline(int i, const char *s, int n, char mark, int lineno) {
    char m = mark; blk_raw(i, &m, 1);
    const char *gut = (mark==2) ? "+ " : (mark==3) ? "- " : "  ";
    char pre[16];
    if (lineno > 0) snprintf(pre, sizeof pre, "%4d %s", lineno, gut);
    else            snprintf(pre, sizeof pre, "     %s", gut);
    blk_raw(i, pre, 7);
    blk_raw(i, s, (size_t)n);
    blk_raw(i, "\n", 1);
}
/* 1-based file line where `needle` begins, or -1 (unreadable / not found) */
static int file_start_line(const char *path, const char *needle) {
    if (!path || !needle || !*needle) return -1;
    FILE *f = fopen(path, "rb"); if (!f) return -1;
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return -1; }
    long sz = ftell(f); if (sz <= 0 || sz > 8*1024*1024) { fclose(f); return -1; }
    rewind(f);
    char *buf = malloc((size_t)sz + 1); if (!buf) { fclose(f); return -1; }
    size_t rd = fread(buf, 1, (size_t)sz, f); fclose(f); buf[rd] = 0;
    char *pos = strstr(buf, needle); int line = -1;
    if (pos) { line = 1; for (char *q = buf; q < pos; q++) if (*q == '\n') line++; }
    free(buf); return line;
}
/* unified-ish line diff: trim common prefix/suffix, show changed lines + context.
   old=="" -> new file. start = 1-based file line of old_string (<=0: no numbers).
   Markers: 2 add, 3 del, 4 context (numbered), 6 summary/elision (plain). */
static void emit_diff(int i, const char *o, const char *nw, int start) {
    const char *os[2048]; int ol[2048]; int no = 0;
    const char *ns[2048]; int nl[2048]; int nn = 0;
    for (const char *p = o; *p && no < 2048; ) { const char *e = strchr(p,'\n'); int L = e?(int)(e-p):(int)strlen(p); os[no]=p; ol[no]=L; no++; if(!e)break; p=e+1; }
    for (const char *p = nw; *p && nn < 2048; ) { const char *e = strchr(p,'\n'); int L = e?(int)(e-p):(int)strlen(p); ns[nn]=p; nl[nn]=L; nn++; if(!e)break; p=e+1; }
    int pre = 0;
    while (pre<no && pre<nn && ol[pre]==nl[pre] && !memcmp(os[pre],ns[pre],(size_t)ol[pre])) pre++;
    int suf = 0;
    while (suf<no-pre && suf<nn-pre && ol[no-1-suf]==nl[nn-1-suf] && !memcmp(os[no-1-suf],ns[nn-1-suf],(size_t)ol[no-1-suf])) suf++;
    int del = (no - suf) - pre;            /* ≥0: the suf loop is bounded by no-pre / nn-pre */
    int add = (nn - suf) - pre;
    if (add || del) { char sm[48]; snprintf(sm, sizeof sm, "+%d -%d", add, del); blk_marked(i, sm, 6); }
    const int CTX = 3;
    int cs = pre - CTX; if (cs < 0) cs = 0;
    if (cs > 0) blk_marked(i, "\xe2\x8b\xaf", 6);                       /* ⋯ elided above */
    for (int k = cs;  k < pre;     k++) emit_dline(i, os[k], ol[k], 4, start>0?start+k:0);
    for (int k = pre; k < no-suf;  k++) emit_dline(i, os[k], ol[k], 3, start>0?start+k:0);
    for (int k = pre; k < nn-suf;  k++) emit_dline(i, ns[k], nl[k], 2, start>0?start+k:0);
    int ce = (nn-suf) + CTX; if (ce > nn) ce = nn;
    for (int k = nn-suf; k < ce;   k++) emit_dline(i, ns[k], nl[k], 4, start>0?start+k:0);
    if (ce < nn) blk_marked(i, "\xe2\x8b\xaf", 6);                      /* ⋯ elided below */
}

/* ====================================================== render line list = */
typedef struct { int off; int len; Sty s; } Run;
struct RLine { Run *r; int n, cap; uint32_t rowbg; bool has_rowbg; const char *abase; };  /* rowbg = full-width line bg; abase = arena the runs index into */
static RLine *g_rl; static int g_nrl, g_rlcap;       /* scratch the emitters write into (block_layout points this at a block's cache) */
static char *g_arena; static int g_arn, g_arcap;     /* text backing for runs */
static RLine **g_view; static int g_nview, g_viewcap; /* per-frame draw order: pointers into block caches */
static RLine g_sep;                                   /* shared blank separator line between blocks (n==0) */
static void view_push(RLine *l) {
    if (g_nview == g_viewcap) { g_viewcap = g_viewcap?g_viewcap*2:512; g_view = realloc(g_view, g_viewcap*sizeof*g_view); }
    g_view[g_nview++] = l;
}
/* ---- text selection: mouse drag highlights view lines, Ctrl+C copies them ---- */
static bool g_sel = false, g_seldrag = false;          /* a selection exists / a drag is in progress */
static int g_sel_a_li, g_sel_a_col, g_sel_c_li, g_sel_c_col;  /* anchor + cursor: view-line index, byte/cell column */
static int g_v_hdr, g_v_body, g_v_first;               /* last render's transcript geometry, for mouse hit-testing */
/* self-drawn block cursor — we never enable the hardware cursor, so renders don't hide/show it
   (that toggle was the residual flicker); a drawn block redraws identically → notcurses diffs it away */
static bool g_cur_on = false; static int g_cur_y, g_cur_x; static char g_cur_gc[8] = " ";
/* mouse polish: click-to-position in the input, click an overlay row, double-click word, edge autoscroll */
static int g_in_top, g_in_bot, g_in_lm, g_in_cw;        /* input box geometry, captured each render */
static char g_click_kind = 0;                            /* active overlay: 0 none, 'm' menu, 'r' resume, 'c' choice, 'p' perm */
static int  g_click_row[1024];                           /* screen row → selectable item index (-1 = none) */
static long g_last_click_ms = 0; static int g_last_click_y = -9, g_last_click_x = -9;   /* double-click detection */
static int  g_drag_y = -1;                               /* last drag y — drives edge autoscroll while selecting */

static int arena_put(const char *s, int n) {
    if (g_arn + n + 1 > g_arcap) { while (g_arn+n+1 > g_arcap) g_arcap = g_arcap?g_arcap*2:65536; g_arena = realloc(g_arena, g_arcap); }
    int off = g_arn; memcpy(g_arena + g_arn, s, n); g_arn += n; g_arena[g_arn++] = 0; return off;
}
static RLine *rl_new(void) {
    if (g_nrl == g_rlcap) { int old = g_rlcap; g_rlcap = g_rlcap?g_rlcap*2:256; g_rl = realloc(g_rl, g_rlcap*sizeof*g_rl);
        memset(g_rl + old, 0, (size_t)(g_rlcap - old)*sizeof*g_rl); }   /* new slots start r=NULL,cap=0 */
    RLine *l = &g_rl[g_nrl++];
    l->n = 0; l->rowbg = 0; l->has_rowbg = false; l->abase = NULL;      /* keep l->r / l->cap to reuse the Run[] (no per-frame leak) */
    return l;
}
static void rl_run(RLine *l, const char *s, int n, Sty st) {
    if (n <= 0) return;
    if (l->n == l->cap) { l->cap = l->cap?l->cap*2:4; l->r = realloc(l->r, l->cap*sizeof*l->r); }
    l->r[l->n++] = (Run){ arena_put(s, n), n, st };
}

/* logical-line builder: bytes + per-byte style, then wrap to width */
static char *g_lb; static Sty *g_sb; static int g_lblen, g_lbcap;
static void lb_reset(void) { g_lblen = 0; }
static void lb_add(const char *s, int n, Sty st) {
    if (g_lblen + n > g_lbcap) { while (g_lblen+n > g_lbcap) g_lbcap = g_lbcap?g_lbcap*2:1024;
        g_lb = realloc(g_lb, g_lbcap); g_sb = realloc(g_sb, g_lbcap*sizeof*g_sb); }
    for (int i = 0; i < n; i++) { g_lb[g_lblen] = s[i]; g_sb[g_lblen] = st; g_lblen++; }
}

/* coalesce [a,b) of the logical buffer into runs on one RLine */
static void emit_segment(int a, int b) {
    RLine *l = rl_new();
    int i = a;
    while (i < b) {
        int j = i + 1; while (j < b && sty_eq(g_sb[j], g_sb[i])) j++;
        rl_run(l, g_lb + i, j - i, g_sb[i]); i = j;
    }
}
/* word-wrap the logical buffer to width W into RLines */
static void lb_flush(int W) {
    if (W < 1) W = 1;
    if (g_lblen == 0) { rl_new(); return; }       /* blank line */
    int s = 0;
    while (s < g_lblen) {
        int rem = g_lblen - s;
        if (rem <= W) { emit_segment(s, g_lblen); break; }
        int brk = W; for (int k = W; k > 0; k--) if (g_lb[s+k] == ' ') { brk = k; break; }
        emit_segment(s, s + brk);
        s += brk; while (s < g_lblen && g_lb[s] == ' ') s++;
    }
}

/* ---- lightweight C-ish syntax highlighter (keywords/types/strings/numbers/comments) ---- */
static int kw_in(const char *s, int n, const char *const *list) {
    for (int i = 0; list[i]; i++) if ((int)strlen(list[i]) == n && !memcmp(s, list[i], (size_t)n)) return 1;
    return 0;
}
static int is_kw(const char *s, int n) {
    static const char *const K[] = {"if","else","for","while","do","switch","case","default","return",
        "break","continue","goto","struct","enum","union","typedef","sizeof","static","const","extern",
        "inline","volatile","register","void","class","public","private","protected","new","delete",
        "import","export","from","def","function","let","var","async","await","yield","try","catch",
        "finally","throw","this","self","lambda","pass","with","as","in","is","and","or","not","true",
        "false","null","nil","None","True","False",NULL};
    return kw_in(s, n, K);
}
static int is_type(const char *s, int n) {
    static const char *const T[] = {"int","char","short","long","float","double","unsigned","signed",
        "bool","size_t","ssize_t","uint8_t","uint16_t","uint32_t","uint64_t","int8_t","int16_t",
        "int32_t","int64_t","FILE","string","str","bytes","auto",NULL};
    return kw_in(s, n, T);
}
/* tokenize a code span into the line builder; each token keeps base.bg (e.g. diff bg) */
static void lb_code(const char *s, int n, Sty base) {
    int i = 0;
    while (i < n) {
        unsigned char c = (unsigned char)s[i];
        if (c=='/' && i+1<n && s[i+1]=='/') { Sty t=base; t.fg=0x7f8388; lb_add(s+i, n-i, t); break; }
        if (c=='/' && i+1<n && s[i+1]=='*') { int j=i+2; while(j+1<n && !(s[j]=='*'&&s[j+1]=='/')) j++; j=(j+1<n)?j+2:n; Sty t=base; t.fg=0x7f8388; lb_add(s+i, j-i, t); i=j; continue; }
        if (c=='#' && i==0) { Sty t=base; t.fg=0x89ddff; lb_add(s+i, n-i, t); break; }
        if (c=='"' || c=='\'') { char q=(char)c; int j=i+1; while(j<n && s[j]!=q){ if(s[j]=='\\'&&j+1<n)j++; j++; } j=(j<n)?j+1:n; Sty t=base; t.fg=0xf3d18e; lb_add(s+i, j-i, t); i=j; continue; }
        if (isdigit(c)) { int j=i; while(j<n && (isalnum((unsigned char)s[j])||s[j]=='.'||s[j]=='_')) j++; Sty t=base; t.fg=0xf78c6c; lb_add(s+i, j-i, t); i=j; continue; }
        if (isalpha(c)||c=='_') { int j=i; while(j<n && (isalnum((unsigned char)s[j])||s[j]=='_')) j++; Sty t=base;
            if (is_kw(s+i,j-i)) t.fg=0xd6a8f5; else if (is_type(s+i,j-i)) t.fg=COL_OV_TITLE;
            lb_add(s+i, j-i, t); i=j; continue; }
        lb_add(s+i, 1, base); i++;
    }
}

/* ====================================================== block emitters === */
static uint32_t kind_fg(Bkind k) {
    switch (k) { case B_USER:return 0x9db4d6; case B_ASSISTANT:return 0xf4f4f4;   /* user = soft periwinkle, distinct from Claude's near-white */
        case B_THINKING:return 0xa4a4a4; case B_TOOL:return 0x5fd7d7;
        case B_RESULT:return 0xdedede; case B_SYS:return 0xa4a4a4; } return 0xf4f4f4;
}

/* inline markdown: **bold**, `code`, leave * and _ literal (snake_case safe) */
static void emit_inline(const char *s, int len, Sty base) {
    Sty cur = base; bool bold = false, code = false;
    int i = 0;
    while (i < len) {
        if (!code && s[i]=='*' && i+1<len && s[i+1]=='*') { bold=!bold; i+=2;
            cur=base; if (bold){cur.bold=true; cur.fg=0xffffff;} continue; }
        if (s[i]=='`') { code=!code; i++; cur=base;
            if (code){cur.fg=0x95d195;} else if (bold){cur.bold=true;cur.fg=0xffffff;} continue; }
        int j = i; while (j < len && s[j] != '`' && !(!code && s[j]=='*' && j+1<len && s[j+1]=='*')) j++;
        lb_add(s + i, j - i, cur); i = j;
    }
}
/* markdown block (assistant / thinking) */
static void emit_markdown(const Block *b, int W) {
    Sty base = STY_DEF; base.fg = kind_fg(b->kind);
    if (b->kind == B_THINKING) { base.dim = true; base.ital = true; }
    if (b->queued) { base.dim = true; base.ital = true; base.fg = 0x6b7a99; }   /* pending: queued, not yet sent */
    const char *s = b->t ? b->t : ""; const char *end = s + b->len;
    const char *p = s; bool fence = false;
    while (p < end) {
        const char *nl = memchr(p, '\n', (size_t)(end - p));
        const char *le = nl ? nl : end; int L = (int)(le - p);
        bool isfence = (L >= 3 && p[0]=='`' && p[1]=='`' && p[2]=='`');
        lb_reset();
        if (isfence) { fence = !fence; }            /* eat the ``` delimiter line */
        else if (fence) {                            /* verbatim code line */
            Sty cs = base; cs.fg = 0xcdcdcd; cs.bg = COL_CODEBG; cs.has_bg = true;
            lb_add(p, L, cs);
        } else if (L > 0 && p[0] == '#') {           /* header */
            int h = 0; while (h < L && p[h]=='#') h++; while (h < L && p[h]==' ') h++;
            Sty hs = base; hs.bold = true; hs.fg = 0x87afff;
            lb_add(p + h, L - h, hs);
        } else {
            const char *tp = p; int tl = L;
            if (p == s && L >= 4 && (unsigned char)p[0] == 0xE2 && p[3] == ' ' &&   /* leading ⏺/✻ marker -> sprite blue */
                (((unsigned char)p[1]==0x8F && (unsigned char)p[2]==0xBA) ||
                 ((unsigned char)p[1]==0x9C && (unsigned char)p[2]==0xBB))) {
                Sty mk = base; mk.fg = COL_BRAND; mk.dim = false; mk.ital = false; mk.bold = true;
                lb_add(p, 4, mk); tp = p + 4; tl = L - 4;
            }
            emit_inline(tp, tl, base);
        }
        if (!isfence) lb_flush(W);
        if (!nl) break;
        p = nl + 1;
    }
}
/* marked tool/diff/result block. Markers: 1 header, 2 add(+), 3 del(-), 4 context, 5 code, 6 plain.
   Diff lines (2/3/4) carry a 7-char "number + gutter" prefix; the code after it is highlighted. */
static void emit_marked(const Block *b, int W, int limit) {
    const char *s = b->t ? b->t : ""; const char *end = s + b->len; const char *p = s;
    int total = 0;                                   /* body (non-header) source lines */
    for (const char *q = s; q < end; ) { const char *nl = memchr(q,'\n',(size_t)(end-q)); const char *le=nl?nl:end;
        char m=(q<le)?q[0]:0; if (m != 1) total++; if (!nl) break; q = nl + 1; }
    int shown = 0;
    while (p < end) {
        const char *nl = memchr(p, '\n', (size_t)(end - p));
        const char *le = nl ? nl : end;
        char mark = (p < le) ? p[0] : 0;
        if (mark != 1 && shown >= limit) {           /* collapse the remainder (ctrl-o expands) */
            char h[64]; snprintf(h, sizeof h, "… +%d lines  (ctrl-o to expand)", total - shown);
            lb_reset(); Sty d = STY_DEF; d.fg = COL_DIM; d.ital = true; lb_add(h, (int)strlen(h), d); lb_flush(W);
            break;
        }
        const char *txt = p + ((mark>=1 && mark<=9) ? 1 : 0);
        int L = (int)(le - txt);
        uint32_t rbg = 0; bool rbgset = false;
        lb_reset();
        if (mark == 2 || mark == 3) {                 /* diff add/del: number, gutter, highlighted code */
            uint32_t bg = (mark==2) ? 0x183a24 : 0x3a1826; rbg = bg; rbgset = true;
            Sty num = STY_DEF; num.fg = 0x8c8c8c; num.bg = bg; num.has_bg = true;
            Sty gut = STY_DEF; gut.fg = (mark==2) ? 0xb6f3b1 : 0xff9bb8; gut.bg = bg; gut.has_bg = true;
            Sty code = STY_DEF; code.fg = 0xf2f2f2; code.bg = bg; code.has_bg = true;
            lb_add(txt, L<5?L:5, num);
            if (L > 5) lb_add(txt+5, (L-5)<2?(L-5):2, gut);
            if (L > 7) lb_code(txt+7, L-7, code);
        } else if (mark == 4) {                       /* context: number + gutter + code (bright-ish) */
            Sty d = STY_DEF; d.fg = 0xc8c8c8;
            lb_add(txt, L<5?L:5, d);
            if (L > 5) lb_add(txt+5, (L-5)<2?(L-5):2, d);
            if (L > 7) lb_add(txt+7, L-7, d);
        } else if (mark == 5) {                       /* fenced code block: highlighted on dark bg */
            rbg = COL_CODEBG; rbgset = true;
            Sty code = STY_DEF; code.fg = 0xf2f2f2; code.bg = COL_CODEBG; code.has_bg = true;
            lb_code(txt, L, code);
        } else if (mark == 1) {                       /* header */
            Sty st = STY_DEF; st.fg = COL_BRAND; st.bold = true; lb_add(txt, L, st);
        } else if (mark == 7) {                       /* todo: completed */
            Sty st = STY_DEF; st.fg = 0x7faf7f; lb_add(txt, L, st);
        } else if (mark == 8) {                       /* todo: in progress */
            Sty st = STY_DEF; st.fg = COL_WARN; st.bold = true; lb_add(txt, L, st);
        } else if (mark == 9) {                       /* todo: pending */
            Sty st = STY_DEF; st.fg = 0xb0b0b0; lb_add(txt, L, st);
        } else {                                      /* 6 / plain: dim */
            Sty st = STY_DEF; st.fg = 0xcacaca; lb_add(txt, L, st);
        }
        int before = g_nrl;
        lb_flush(W);
        if (rbgset) for (int q = before; q < g_nrl; q++) { g_rl[q].rowbg = rbg; g_rl[q].has_rowbg = true; }
        if (mark != 1) shown++;
        if (!nl) break;
        p = nl + 1;
    }
}

/* ====================================================== app state ======== */
static struct notcurses *g_nc; static struct ncplane *g_std;

/* input editor */
static char  g_in[16384]; static int g_ilen, g_icur;   /* utf8 bytes, cursor byte idx */
static char *g_hist[256]; static int g_histn, g_histpos;
static char  g_draft[16384];                            /* stashed while browsing history */
static bool  g_rsearch = false; static char g_rquery[256]; static int g_rqlen = 0, g_rmatch = -1;  /* ctrl+r */
static bool  g_vim = false, g_vins = true; static char g_vop = 0, g_vvisual = 0; static int g_vanchor = 0;  /* vim: on, insert, pending op, visual (v/V) + anchor */
static void visual_range(int *a, int *b);   /* fwd: byte range of the visual selection (defined with vim) */

/* status */
static char g_model[64] = "", g_session[16] = "--------", g_status[32] = "idle";
static char g_version[64] = "", g_cwd[512] = "", g_plan[40] = "";   /* persistent header info */
static char g_sid[64] = "";                                         /* full session id (for --resume restarts) */
static char g_model_arg[64] = "", g_effort[16] = "";               /* spawn flags: --model alias, --effort level */
static char g_bin[512] = "";                                       /* --claude-bin: engine path (else $CRUD_CLAUDE_BIN / "claude") */
static char g_agent_arg[64] = "";                                  /* --agent: session agent, passed to the engine */
static char g_adddir[8][512]; static int g_nadddir = 0;            /* --add-dir: extra tool-access dirs, passed to the engine */
static char g_pending_name[140] = "";                              /* -n/--name: applied to the session once its id is known */
static char *g_mcp = NULL;                                          /* mcp_servers array from init (for /mcp) */
/* generic choice picker (model / effort / rewind), command-palette styled */
static bool g_choice_open = false; static char g_choice_kind = 0;
static char g_choice[24][120]; static int g_choice_ref[24]; static int g_nchoice = 0, g_chsel = 0;
static char g_choice_title[32];
static double g_in_tok = 0, g_out_tok = 0; static long g_reset_at = 0;   /* token usage + 5h reset */
static double g_cost = 0, g_dur_ms = 0;                                  /* cumulative session cost + wall time */
static char g_permmode[24] = "default";
static bool g_busy = false, g_engine_alive = true, g_quit = false;
static bool g_confirm_quit = false; static int g_qsel = 0;   /* quit-confirmation modal (Yes/No): ctrl-c on empty prompt, or typed /quit */
static volatile sig_atomic_t g_sigint = 0, g_sigterm = 0;    /* ctrl-c -> confirm; TERM/QUIT -> graceful */
static char *g_queue[16]; static int g_queue_blk[16]; static int g_nqueue = 0;   /* messages typed while busy (+ their blocks); sent on turn end */
static char g_toast[80] = ""; static long g_toast_until = 0;                     /* transient footer notice, e.g. "✓ copied" */
static char  g_last_tool[48] = "";                          /* name of the most recent tool_use */
static void  dispatch_user(const char *text);               /* fwd: build + send a user turn */
static void  fmt_reset(char *o, long reset);                /* fwd: "3h"/"4d" remaining until a reset epoch */
static void  fmt_k(char *o, double n);                      /* fwd: compact token count, "62k" / "950" */
static void  session_name_set(const char *id, const char *name);   /* fwd: persist a session's custom name */
static int g_scroll = 0;
static bool g_expand = false;                                            /* ctrl-o: expand collapsed tool output */
static int g_turn_n = 0; static long g_turn_start = 0; static long g_spin_phase = -1;  /* working spinner (wall-clock driven) */
static double g_think_est = 0, g_turn_bytes = 0;                          /* realtime token estimate */

/* permission */
static bool g_perm = false, g_perm_isplan = false;      /* isplan: ExitPlanMode approval, not a tool grant */
static char *g_perm_rid, *g_perm_tool, *g_perm_input, *g_perm_desc, *g_perm_sugg;
/* numbered prompt options: 0=Yes, 1..g_nopt=suggestions, g_nopt+1=No */
static char *g_opt_sugg[8]; static char *g_opt_label[8]; static int g_nopt = 0, g_psel = 0;

/* slash commands (name + description) for autocomplete */
static char *g_cmds[768]; static char *g_cdesc[768]; static int g_ncmds;
static bool g_capmd = false;                            /* engine commands captured yet? */

/* autocomplete menu */
static bool g_menu = false; static int g_msel = 0;
static char *g_match[768]; static char *g_mdesc[768]; static int g_nmatch = 0;
static int g_tok_start = 0;                              /* byte idx where current token begins */
static char g_menu_kind = 0;                             /* '/' or '@' */
static bool g_resized = false;                           /* force full repaint after resize */

/* engine pipe */
static int g_wfd = -1, g_efd = -1; static pid_t g_child = -1;
static char *g_acc; static size_t g_accl, g_acccap;     /* engine output accumulator (reset on restart) */
static void restart_engine(const char *resume_id, bool forked);  /* fwd: kill+respawn engine (optionally resumed / forked) */
static long now_ms(void);                            /* fwd: monotonic milliseconds */
static void clipboard_copy(const char *s, int n);   /* fwd: write to the system clipboard */

/* session picker (resume) */
typedef struct { char id[40]; char label[140]; char name[140]; char path[1200]; long mtime; } Sess;
static Sess g_sess[64]; static int g_nsess = 0, g_ssel = 0; static bool g_resume_open = false;

static void send_line(const char *json) {
    if (g_wfd < 0) return;
    size_t n = strlen(json);
    ssize_t r = write(g_wfd, json, n); (void)r; r = write(g_wfd, "\n", 1); (void)r;
}

static const char *mode_label(const char *m) {
    if (!strcmp(m, "acceptEdits")) return "accept edits on";
    if (!strcmp(m, "plan")) return "plan mode on";
    if (!strcmp(m, "bypassPermissions")) return "bypass permissions on";
    return "ask each time";
}
static void set_mode(const char *m) {
    snprintf(g_permmode, sizeof g_permmode, "%s", m);
    char b[160]; snprintf(b, sizeof b, "{\"type\":\"control_request\",\"request_id\":\"crud-cli-mode\","
        "\"request\":{\"subtype\":\"set_permission_mode\",\"mode\":\"%s\"}}", m);
    send_line(b);
}
static void cycle_mode(void) {        /* shift+tab: default -> acceptEdits -> plan -> default */
    if (!strcmp(g_permmode, "default")) set_mode("acceptEdits");
    else if (!strcmp(g_permmode, "acceptEdits")) set_mode("plan");
    else set_mode("default");
}
static void interrupt_turn(void) {    /* Esc: abort the in-flight turn; engine keeps work done so far */
    send_line("{\"type\":\"control_request\",\"request_id\":\"crud-cli-int\","
              "\"request\":{\"subtype\":\"interrupt\"}}");
    g_busy = false;                   /* unlock input immediately so you can redirect */
    g_cur_asst = -1; g_cur_think = -1; /* end the current streaming blocks */
    snprintf(g_status, sizeof g_status, "interrupted");
}

/* ====================================================== event handling === */
static void add_cmd(const char *name, const char *desc) {
    for (int i = 0; i < g_ncmds; i++) if (!strcmp(g_cmds[i], name)) return;   /* dedupe */
    if (g_ncmds < 768) { g_cmds[g_ncmds] = strdup(name); g_cdesc[g_ncmds] = strdup(desc?desc:""); g_ncmds++; }
}
/* client-side commands the real TUI provides (not in the engine stream).
   NOTE: several are not wired to behaviour yet — shown for parity/discovery. */
static void seed_builtin_cmds(void) {
    /* authoritative client-side/built-in set (docs: code.claude.com/docs/en/commands) */
    static const char *bi[][2] = {
        {"clear","Start a new session, keeping project memory"},
        {"compact","Summarize the conversation to free up context"},
        {"context","Show current context usage"},
        {"cost","Show session cost and duration"},
        {"config","Open the configuration UI"},
        {"resume","Resume or fork an earlier conversation"},
        {"rename","Rename the current conversation"},
        {"rewind","Roll code and conversation back to a checkpoint"},
        {"recap","Generate a session recap now"},
        {"branch","Fork the conversation into a new session"},
        {"copy","Copy Claude's last response to the clipboard"},
        {"plan","Switch into plan mode"},
        {"model","Switch the model for this session"},
        {"effort","Adjust how much reasoning to spend"},
        {"agents","Manage subagents"}, {"mcp","Manage MCP servers"},
        {"memory","Edit CLAUDE.md memory files"},
        {"permissions","Set tool approval rules"},
        {"hooks","Manage hooks"}, {"add-dir","Add a directory to the workspace"},
        {"help","Show help and available commands"},
        {"init","Generate a starter CLAUDE.md"},
        {"vim","Toggle vim editing mode"},
        {"keybindings","Configure keybindings"},
        {"statusline","Configure the status line"},
        {"terminal-setup","Install terminal keybindings"},
        {"status","Show session status"}, {"usage","Show plan usage and limits"},
        {"diff","Show what changed"}, {"tasks","List background tasks"},
        {"btw","Ask a quick side question (ephemeral)"},
        {"export","Export the conversation"},
        {"release-notes","View release notes"},
        {"remote-env","Choose the default cloud-agent environment"},
        {"reload-plugins","Activate pending plugin changes"},
        {"feedback","Report a bug with session context"},
        {"doctor","Diagnose install and runtime issues"},
        {"login","Log in to your account"}, {"logout","Log out"},
        {"privacy-settings","Open privacy settings"},
        {NULL,NULL}
    };
    for (int i = 0; bi[i][0]; i++) add_cmd(bi[i][0], bi[i][1]);
}
static void capture_cmds(const char *L) {           /* pull name+description from init reply */
    const char *p = strstr(L, "\"commands\"");
    if (!p) p = strstr(L, "\"slash_commands\"");
    if (!p) return;
    while (g_ncmds < 760) {
        const char *nm = strstr(p, "\"name\"");
        if (!nm) break;
        char *name = j_str(nm, "name");
        char *desc = j_str(nm, "description");
        if (name) add_cmd(name, desc);
        free(name); free(desc);
        p = nm + 6;
    }
}

/* human label for one permission-suggestion object */
static char *perm_label(const char *o) {
    char buf[320] = "";
    char *type = j_str(o, "type");
    if (type && !strcmp(type, "setMode")) {
        char *m = j_str(o, "mode");
        if (m && !strcmp(m, "acceptEdits")) snprintf(buf, sizeof buf, "Yes, and accept all edits this session");
        else if (m && !strcmp(m, "plan")) snprintf(buf, sizeof buf, "Yes, and switch to plan mode");
        else if (m && !strcmp(m, "bypassPermissions")) snprintf(buf, sizeof buf, "Yes, and bypass permissions this session");
        else snprintf(buf, sizeof buf, "Yes, and set mode: %s", m ? m : "?");
        free(m);
    } else if (type && !strcmp(type, "addRules")) {
        char *tn = j_str(o, "toolName"); char *rc = j_str(o, "ruleContent");
        if (tn && rc) snprintf(buf, sizeof buf, "Yes, and always allow %s(%s)", tn, rc);
        else if (tn)  snprintf(buf, sizeof buf, "Yes, and always allow %s", tn);
        else snprintf(buf, sizeof buf, "Yes, and add an allow rule");
        free(tn); free(rc);
    } else if (type && !strcmp(type, "addDirectories")) {
        const char *dp = strstr(o, "directories"); char dir[256] = "";
        if (dp) { const char *q = strchr(dp, '['); if (q && (q = strchr(q, '"'))) { q++; const char *e = q;
            while (*e && *e != '"') { e++; }
            int dl = (int)(e - q); if (dl > 0 && dl < 255) { memcpy(dir, q, (size_t)dl); dir[dl] = 0; } } }
        snprintf(buf, sizeof buf, "Yes, and add %s to allowed dirs", dir[0] ? dir : "directory");
    } else {
        snprintf(buf, sizeof buf, "Yes, and apply: %s", type ? type : "suggestion");
    }
    free(type);
    return strdup(buf);
}
/* split permission_suggestions into per-option objects + labels */
static void parse_perm_opts(void) {
    for (int i = 0; i < g_nopt; i++) { free(g_opt_sugg[i]); free(g_opt_label[i]); }
    g_nopt = 0; g_psel = 0;
    if (!g_perm_sugg) return;
    const char *p = g_perm_sugg;
    while (*p && g_nopt < 8) {
        while (*p && *p != '{') p++;
        if (!*p) break;
        const char *st = p; p = j_obj_end(p);
        int n = (int)(p - st); char *obj = malloc((size_t)n + 1); if (!obj) break;
        memcpy(obj, st, (size_t)n); obj[n] = 0;
        g_opt_sugg[g_nopt] = obj; g_opt_label[g_nopt] = perm_label(obj); g_nopt++;
    }
}
/* identity cache: model/plan/version arrive only on the first turn's system/init, so persist them
   and pre-seed on the next cold start (parity with the official CLI showing identity immediately). */
static void ident_path(char *o, size_t n) { snprintf(o, n, "/tmp/crud-ident-%d", (int)getuid()); }
static void ident_save(void) {
    char p[64]; ident_path(p, sizeof p); FILE *f = fopen(p, "w"); if (!f) return;
    fprintf(f, "%s\n%s\n%s\n", g_model, g_plan, g_version); fclose(f);
}
static void ident_load(void) {
    char p[64]; ident_path(p, sizeof p); FILE *f = fopen(p, "r"); if (!f) return;
    char m[64]="", pl[40]="", v[64]="";
    if (fgets(m, sizeof m, f))  { m[strcspn(m, "\n")]  = 0; if (m[0]  && !g_model[0])   snprintf(g_model,   sizeof g_model,   "%s", m);  }
    if (fgets(pl, sizeof pl, f)) { pl[strcspn(pl, "\n")] = 0; if (pl[0] && !g_plan[0])    snprintf(g_plan,    sizeof g_plan,    "%s", pl); }
    if (fgets(v, sizeof v, f))  { v[strcspn(v, "\n")]  = 0; if (v[0]  && !g_version[0]) snprintf(g_version, sizeof g_version, "%s", v);  }
    fclose(f);
}
/* render a tool_use into block b: per-tool header + diff/checklist. `in` = raw input object JSON.
   nested = a subagent's tool (parent_tool_use_id set) → indent under the Task with a branch glyph.
   Shared by live streaming (on_line) and transcript replay (load_transcript). */
static void render_tool(int b, const char *nm, const char *in, bool nested) {
    const char *L0 = nested ? "  ⎿ " : "● ";          /* header lead: branch when nested */
    char *fp = in ? j_str(in, "file_path") : NULL;
    if (!strcmp(nm, "Bash")) {
        char *cmd = in ? j_str(in, "command") : NULL;
        char *u = cmd ? j_unescape_dup(cmd) : NULL;
        char hdr[256]; snprintf(hdr, sizeof hdr, "%s$ %s", L0, u ? u : "");
        blk_marked(b, hdr, 1); free(cmd); free(u);
    } else if (!strcmp(nm, "Read")) {
        char hdr[512]; snprintf(hdr, sizeof hdr, "%sRead %s", L0, fp ? fp : "");
        blk_marked(b, hdr, 1);
    } else if (!strcmp(nm, "Write")) {
        char hdr[512]; snprintf(hdr, sizeof hdr, "%sWrite %s", L0, fp ? fp : ""); blk_marked(b, hdr, 1);
        if (!nested) {
            char *c = in ? j_str(in, "content") : NULL;
            char *u = c ? j_unescape_dup(c) : strdup("");
            emit_diff(b, "", u, 1);          /* new file = all additions, from line 1 */
            free(u); free(c);
        }
    } else if (!strcmp(nm, "Edit")) {
        char hdr[512]; snprintf(hdr, sizeof hdr, "%sEdit %s", L0, fp ? fp : ""); blk_marked(b, hdr, 1);
        if (!nested) {
            char *os = in ? j_str(in, "old_string") : NULL;
            char *ns = in ? j_str(in, "new_string") : NULL;
            char *ou = os ? j_unescape_dup(os) : strdup("");
            char *nu = ns ? j_unescape_dup(ns) : strdup("");
            emit_diff(b, ou, nu, file_start_line(fp, ou));   /* real line numbers from the file */
            free(ou); free(nu); free(os); free(ns);
        }
    } else if (!strcmp(nm, "TodoWrite")) {               /* live checklist (☐ pending · ▸ active · ✔ done) */
        char th[32]; snprintf(th, sizeof th, "%sUpdate todos", L0); blk_marked(b, th, 1);
        char *todos = in ? j_arr(in, "todos") : NULL;
        if (todos) {
            const char *tp = todos;
            while ((tp = strchr(tp, '{')) != NULL) {
                const char *st = tp; const char *q = j_obj_end(tp);
                size_t ol = (size_t)(q - st); char *obj = malloc(ol + 1); memcpy(obj, st, ol); obj[ol] = 0;
                char *content = j_str(obj, "content"); char *status = j_str(obj, "status");
                char *cu = content ? j_unescape_dup(content) : strdup("");
                char mk = 9; const char *box = "☐ ";
                if (status && !strcmp(status, "completed"))        { mk = 7; box = "✔ "; }
                else if (status && !strcmp(status, "in_progress")) { mk = 8; box = "▸ "; }
                char line[1200]; snprintf(line, sizeof line, "  %s%s", box, cu);
                blk_marked(b, line, mk);
                free(content); free(status); free(cu); free(obj);
                tp = q;
            }
            free(todos);
        }
    } else {
        char hdr[512]; char *u = in ? j_unescape_dup(in) : NULL;
        snprintf(hdr, sizeof hdr, "%s%s %s", L0, nm, u ? u : ""); blk_marked(b, hdr, 1); free(u);
    }
    free(fp);
}
/* cap an oversized string with a "… (truncated)" marker (caller guarantees capacity ≥ budget) */
static void truncate_marker(char *s, int budget) {
    if ((int)strlen(s) > budget) strcpy(s + budget - 40, "\n… (truncated)");
}
static void on_line(const char *L) {
    if (strstr(L, "\"type\":\"stream_event\"")) {
        if (strstr(L, "\"text_delta\"")) {
            char *t = j_str(L, "text");
            if (t) { if (g_cur_asst < 0) { g_cur_asst = blk_new(B_ASSISTANT); blk_str(g_cur_asst, "⏺ "); } blk_unesc(g_cur_asst, t); g_turn_bytes += strlen(t); free(t); }
        } else if (strstr(L, "\"thinking_delta\"")) {
            char *t = j_str(L, "thinking");
            if (t) { if (g_cur_think < 0) { g_cur_think = blk_new(B_THINKING); blk_str(g_cur_think, "✻ "); } blk_unesc(g_cur_think, t); g_turn_bytes += strlen(t); free(t); }
        } else if (strstr(L, "\"message_start\"")) {
            g_cur_asst = -1; g_cur_think = -1; snprintf(g_status, sizeof g_status, "responding");
        }
        return;
    }
    char *type = j_str(L, "type"); if (!type) return;

    if (!strcmp(type, "assistant")) {
        const char *tu = strstr(L, "\"tool_use\"");
        if (tu) {
            static char last_id[80];
            char *id = j_str(tu, "id");
            if (!id || strcmp(id, last_id)) {
                if (id) snprintf(last_id, sizeof last_id, "%s", id);
                char *name = j_str(tu, "name"); char *in = j_obj(tu, "input");
                int b = blk_new(B_TOOL);
                const char *nm = name ? name : "tool";
                snprintf(g_last_tool, sizeof g_last_tool, "%s", nm);   /* for result-suppression / nesting */
                /* a subagent's tool carries parent_tool_use_id → render it nested under the Task */
                bool nested = strstr(L, "\"parent_tool_use_id\":\"") != NULL;
                render_tool(b, nm, in, nested);
                free(name); free(in);
                snprintf(g_status, sizeof g_status, "tool");
            }
            free(id);
        }
    } else if (!strcmp(type, "user")) {
        const char *tr = strstr(L, "\"tool_result\"");
        if (tr && strcmp(g_last_tool, "TodoWrite")) {   /* TodoWrite's result is noise; the checklist is enough */
            char *c = j_str(tr, "content");
            bool err = strstr(tr, "\"is_error\":true") != NULL;
            int b = blk_new(B_RESULT);
            char *u = c ? j_unescape_dup(c) : NULL;
            /* cap very long output */
            if (u) truncate_marker(u, 4000);
            blk_marked(b, u ? u : "(no output)", err ? 3 : 4);
            free(u); free(c);
        }
    } else if (!strcmp(type, "control_request") && strstr(L, "\"can_use_tool\"")) {
        free(g_perm_rid); free(g_perm_tool); free(g_perm_input); free(g_perm_desc); free(g_perm_sugg);
        g_perm_rid = j_str(L, "request_id"); g_perm_tool = j_str(L, "tool_name");
        g_perm_input = j_obj(L, "input"); g_perm_desc = j_str(L, "description");
        g_perm_sugg = j_arr(L, "permission_suggestions");   /* the engine's scoped suggestions */
        parse_perm_opts();                                  /* build the numbered options */
        g_perm_isplan = g_perm_tool && !strcmp(g_perm_tool, "ExitPlanMode");
        if (g_perm_isplan && g_perm_input) {                /* show the proposed plan in the transcript */
            char *plan = j_str(g_perm_input, "plan");
            if (plan) { int pb = blk_new(B_ASSISTANT); blk_str(pb, "⏺ Plan\n\n"); blk_unesc(pb, plan); free(plan); g_scroll = 0; }
        }
        g_perm = true; snprintf(g_status, sizeof g_status, g_perm_isplan ? "plan ready" : "permission?");
        { ssize_t bw = write(STDOUT_FILENO, "\a", 1); (void)bw; }   /* bell: Claude is blocked waiting on you */
    } else if (!strcmp(type, "result")) {
        double newin = j_num(L, "input_tokens");    /* context size of last turn */
        if (g_in_tok > 60000 && newin > 0 && newin < g_in_tok * 0.6) {   /* engine auto-compacted the context */
            int b = blk_new(B_SYS); blk_str(b, "↯ context auto-compacted"); g_scroll = 0;
        }
        g_in_tok = newin;
        g_out_tok += j_num(L, "output_tokens");     /* cumulative session output */
        g_cost += j_num(L, "total_cost_usd");       /* cumulative session cost */
        g_dur_ms += j_num(L, "duration_ms");        /* cumulative wall time */
        g_busy = false; snprintf(g_status, sizeof g_status, "idle");
        long dur = (long)time(NULL) - g_turn_start;
        if (g_nqueue > 0) {                         /* a message was queued while busy — send it now */
            char *next = g_queue[0]; int nb = g_queue_blk[0];
            memmove(g_queue, g_queue + 1, (size_t)(g_nqueue - 1) * sizeof *g_queue);
            memmove(g_queue_blk, g_queue_blk + 1, (size_t)(g_nqueue - 1) * sizeof *g_queue_blk); g_nqueue--;
            if (nb >= 0 && nb < (int)g_nblk) { g_blk[nb].queued = false; g_blk[nb].ver++; }   /* now sent → re-wrap as a normal user block */
            dispatch_user(next); free(next);
        } else if (dur >= 8) {
            ssize_t bw = write(STDOUT_FILENO, "\a", 1); (void)bw;   /* bell when a long turn finishes */
        }
    } else if (!strcmp(type, "rate_limit_event")) {
        const char *ri = strstr(L, "\"rate_limit_info\"");
        if (ri) {
            char *t = j_str(ri, "rateLimitType"); double ra = j_num(ri, "resetsAt");
            if (t && !strcmp(t, "five_hour")) g_reset_at = (long)ra;
            free(t);
        }
    } else if (!strcmp(type, "system")) {
        char *sub = j_str(L, "subtype");
        if (sub && !strcmp(sub, "init")) {
            char *m = j_str(L, "model"); if (m){snprintf(g_model,sizeof g_model,"%s",m);free(m);}
            char *s = j_str(L, "session_id"); if (s){snprintf(g_sid,sizeof g_sid,"%s",s); snprintf(g_session,sizeof g_session,"%.8s",s);
                if (g_pending_name[0]) { session_name_set(g_sid, g_pending_name); g_pending_name[0] = 0; }   /* -n/--name */
                free(s);}
            char *v = j_str(L, "claude_code_version"); if (v){snprintf(g_version,sizeof g_version,"%s",v);free(v);}
            char *cw = j_str(L, "cwd"); if (cw){snprintf(g_cwd,sizeof g_cwd,"%s",cw);free(cw);}
            char *pl = j_str(L, "subscriptionType"); if (pl){snprintf(g_plan,sizeof g_plan,"%s",pl);free(pl);}
            free(g_mcp); g_mcp = j_arr(L, "mcp_servers");   /* for /mcp */
            if (!g_capmd) { capture_cmds(L); g_capmd = (g_ncmds > 45); }
            ident_save();                          /* persist identity for the next cold start */
        } else if (sub && !strcmp(sub, "status")) {
            char *st = j_str(L, "status"); if (st){snprintf(g_status,sizeof g_status,"%s",st);free(st);}
        } else if (sub && !strcmp(sub, "thinking_tokens")) {
            g_think_est = j_num(L, "estimated_tokens");           /* live token meter for spinner */
        }
        free(sub);
    } else if (!strcmp(type, "control_response")) {
        if (strstr(L, INIT_ID)) {
            if (!g_capmd) { capture_cmds(L); g_capmd = (g_ncmds > 45); }
            if (!g_plan[0])    { char *p = j_str(L, "subscriptionType");      if (p) { snprintf(g_plan, sizeof g_plan, "%s", p); free(p); } }
            if (!g_model[0])   { char *m = j_str(L, "model");                 if (m) { snprintf(g_model, sizeof g_model, "%s", m); free(m); } }
            if (!g_version[0]) { char *v = j_str(L, "claude_code_version");   if (v) { snprintf(g_version, sizeof g_version, "%s", v); free(v); } }
            ident_save();
        }
    }
    free(type);
}

/* execute a numbered option: 0 = Yes (once), 1..g_nopt = apply that one suggestion, g_nopt+1 = No */
static void answer_opt(int opt) {
    if (!g_perm) return;
    int last = g_nopt + 1;
    if (opt < 0) opt = 0;
    if (opt > last) opt = last;
    size_t cap = (g_perm_input?strlen(g_perm_input):2) + (g_perm_sugg?strlen(g_perm_sugg):2) + 384;
    char *resp = malloc(cap);
    if (opt == last)                                 /* No */
        snprintf(resp, cap, "{\"type\":\"control_response\",\"response\":{\"subtype\":\"success\","
            "\"request_id\":\"%s\",\"response\":{\"behavior\":\"deny\",\"message\":\"Denied by user\"}}}",
            g_perm_rid?g_perm_rid:"");
    else if (opt == 0)                               /* Yes, this time only */
        snprintf(resp, cap, "{\"type\":\"control_response\",\"response\":{\"subtype\":\"success\","
            "\"request_id\":\"%s\",\"response\":{\"behavior\":\"allow\",\"updatedInput\":%s}}}",
            g_perm_rid?g_perm_rid:"", g_perm_input?g_perm_input:"{}");
    else {                                           /* apply exactly the chosen suggestion */
        const char *sug = g_opt_sugg[opt-1];
        snprintf(resp, cap, "{\"type\":\"control_response\",\"response\":{\"subtype\":\"success\","
            "\"request_id\":\"%s\",\"response\":{\"behavior\":\"allow\",\"updatedInput\":%s,\"updatedPermissions\":[%s]}}}",
            g_perm_rid?g_perm_rid:"", g_perm_input?g_perm_input:"{}", sug);
        char *m = j_str(sug, "mode"); if (m) { snprintf(g_permmode, sizeof g_permmode, "%s", m); free(m); }  /* footer follows setMode */
    }
    send_line(resp); free(resp);
    g_perm = false; g_perm_isplan = false; snprintf(g_status, sizeof g_status, opt == last ? "idle" : "responding");
}

/* ====================================================== input editor ===== */
static int utf8_prev(const char *s, int i){ if(i<=0)return 0; i--; while(i>0&&((unsigned char)s[i]&0xC0)==0x80)i--; return i; }
static int utf8_next(const char *s, int i, int len){ if(i>=len)return len; i++; while(i<len&&((unsigned char)s[i]&0xC0)==0x80)i++; return i; }

/* ---- input undo: snapshot the buffer before edits; contiguous edits at the same spot coalesce ---- */
#define UNDO_MAX 100
static char *g_undo_s[UNDO_MAX]; static int g_undo_c[UNDO_MAX]; static int g_undo_n = 0;
static int g_undo_at = -1;                              /* cursor where the next edit coalesces; -1 = break the run */
static void undo_push(void) {                           /* snapshot the current buffer (deduped against the top) */
    if (g_undo_n > 0 && !strcmp(g_undo_s[g_undo_n-1], g_in)) return;
    if (g_undo_n == UNDO_MAX) { free(g_undo_s[0]);
        memmove(g_undo_s, g_undo_s+1, (UNDO_MAX-1)*sizeof*g_undo_s);
        memmove(g_undo_c, g_undo_c+1, (UNDO_MAX-1)*sizeof(int)); g_undo_n--; }
    g_undo_s[g_undo_n] = strdup(g_in); g_undo_c[g_undo_n] = g_icur; g_undo_n++;
}
static void undo_mark(void) { if (g_icur != g_undo_at) undo_push(); }   /* call BEFORE a mutation */

static void in_insert(const char *s, int n) {
    if (g_ilen + n >= (int)sizeof g_in - 1) return;
    undo_mark();
    memmove(g_in + g_icur + n, g_in + g_icur, (size_t)(g_ilen - g_icur));
    memcpy(g_in + g_icur, s, (size_t)n); g_ilen += n; g_icur += n; g_in[g_ilen] = 0;
    g_undo_at = g_icur;
}
static void in_backspace(void) {
    if (g_icur == 0) return;
    undo_mark();
    int p = utf8_prev(g_in, g_icur);
    memmove(g_in + p, g_in + g_icur, (size_t)(g_ilen - g_icur)); g_ilen -= (g_icur - p); g_icur = p; g_in[g_ilen] = 0;
    g_undo_at = g_icur;
}
static void in_delete(void) {
    if (g_icur >= g_ilen) return;
    undo_mark();
    int nx = utf8_next(g_in, g_icur, g_ilen);
    memmove(g_in + g_icur, g_in + nx, (size_t)(g_ilen - nx)); g_ilen -= (nx - g_icur); g_in[g_ilen] = 0;
    g_undo_at = g_icur;
}
static int line_start(int i){ while(i>0 && g_in[i-1]!='\n') i--; return i; }
static int line_end(int i){ while(i<g_ilen && g_in[i]!='\n') i++; return i; }
static void in_clear(void){ g_ilen = 0; g_icur = 0; g_in[0] = 0; }
static void in_set(const char *s){ in_clear(); int n=(int)strlen(s); if(n>(int)sizeof g_in-1)n=sizeof g_in-1; memcpy(g_in,s,(size_t)n); g_ilen=n; g_icur=n; g_in[n]=0; }
/* restore the buffer to the snapshot before the most recent edit group */
static void undo_apply(void) {
    while (g_undo_n > 0 && !strcmp(g_undo_s[g_undo_n-1], g_in)) { free(g_undo_s[g_undo_n-1]); g_undo_n--; }
    if (g_undo_n == 0) return;
    g_undo_n--;
    int cur = g_undo_c[g_undo_n];
    in_set(g_undo_s[g_undo_n]); free(g_undo_s[g_undo_n]);
    g_icur = cur <= g_ilen ? cur : g_ilen;
    g_undo_at = -1;
}
/* ctrl+r: most-recent-first history entry containing g_rquery, starting at index `from` (-1 = none) */
static void rsearch_find(int from) {
    g_rmatch = -1;
    if (from >= g_histn) from = g_histn - 1;
    for (int i = from; i >= 0; i--)
        if (strstr(g_hist[i], g_rquery)) { g_rmatch = i; return; }
}

static void hist_prev(void) {
    if (g_histn == 0) return;
    if (g_histpos == g_histn) { memcpy(g_draft, g_in, (size_t)g_ilen+1); }   /* stash draft */
    if (g_histpos > 0) { g_histpos--; in_set(g_hist[g_histpos]); }
}
static void hist_next(void) {
    if (g_histpos >= g_histn) return;
    g_histpos++;
    if (g_histpos == g_histn) in_set(g_draft); else in_set(g_hist[g_histpos]);
}

/* ---- readline-style kill buffer + word/line motions ---- */
static char g_kill[16384]; static int g_killn = 0; static bool g_kill_linewise = false;  /* yanked text is a whole line → p pastes below */
static void kill_range(int a, int b) {                 /* delete [a,b) into kill buffer */
    if (a < 0) a = 0;
    if (b > g_ilen) b = g_ilen;
    if (a >= b) return;
    undo_mark();
    int n = b - a;
    if (n < (int)sizeof g_kill) { memcpy(g_kill, g_in + a, (size_t)n); g_killn = n; g_kill_linewise = false; }
    memmove(g_in + a, g_in + b, (size_t)(g_ilen - b)); g_ilen -= n; g_in[g_ilen] = 0;
    if (g_icur >= b) g_icur -= n; else if (g_icur > a) g_icur = a;
    g_undo_at = g_icur;
}
static void kill_to_eol(void) { kill_range(g_icur, line_end(g_icur)); }   /* Ctrl+K */
static void kill_to_bol(void) { kill_range(line_start(g_icur), g_icur); } /* Ctrl+U */
static int  word_left(int i)  { while (i>0 && (g_in[i-1]==' '||g_in[i-1]=='\n')) i--; while (i>0 && g_in[i-1]!=' ' && g_in[i-1]!='\n') i--; return i; }
static int  word_right(int i) { while (i<g_ilen && (g_in[i]==' '||g_in[i]=='\n')) i++; while (i<g_ilen && g_in[i]!=' ' && g_in[i]!='\n') i++; return i; }
static void kill_word(void)   { kill_range(word_left(g_icur), g_icur); }  /* Ctrl+W */
static void yank(void)        { if (g_killn > 0) in_insert(g_kill, g_killn); } /* Ctrl+Y */
static void cursor_up(void) {                          /* cursor up, or history at top edge */
    if (line_start(g_icur) == 0) hist_prev();
    else { int col = g_icur - line_start(g_icur); int pe = line_start(g_icur)-1; int ps = line_start(pe); g_icur = ps+col < pe ? ps+col : pe; }
}
static void cursor_down(void) {                        /* cursor down, or history at bottom edge */
    if (line_end(g_icur) == g_ilen) hist_next();
    else { int col = g_icur - line_start(g_icur); int ns = line_end(g_icur)+1; int ne = line_end(ns); g_icur = ns+col < ne ? ns+col : ne; }
}

/* ====================================================== autocomplete ===== */
static const char *ci_strstr(const char *h, const char *n) {     /* case-insensitive substring */
    if (!*n) return h;
    for (; *h; h++) { const char *a=h,*b=n;
        while (*a && *b && tolower((unsigned char)*a)==tolower((unsigned char)*b)) { a++; b++; }
        if (!*b) return h; }
    return NULL;
}
static void menu_clear(void){ for(int i=0;i<g_nmatch;i++){ free(g_match[i]); free(g_mdesc[i]); } g_nmatch=0; g_menu=false; g_msel=0; }

static void menu_update(void) {
    menu_clear();
    /* current token = from last space/newline before cursor to cursor */
    int ts = g_icur; while (ts > 0 && g_in[ts-1] != ' ' && g_in[ts-1] != '\n') ts--;
    int tlen = g_icur - ts; if (tlen <= 0) return;
    char tok[1024]; if (tlen > 1023) return; memcpy(tok, g_in+ts, (size_t)tlen); tok[tlen]=0;
    g_tok_start = ts;
    if (tok[0] == '/' && ts == 0) {                  /* slash command at line start (name + description search) */
        g_menu_kind = '/'; const char *pre = tok + 1;
        for (int pass = 0; pass < 2 && g_nmatch < 768; pass++)
            for (int i = 0; i < g_ncmds && g_nmatch < 768; i++) {
                int nameHit = ci_strstr(g_cmds[i], pre) != NULL;
                int descHit = g_cdesc[i] && ci_strstr(g_cdesc[i], pre) != NULL;
                if (pass == 0 ? !nameHit : (nameHit || !descHit)) continue;   /* pass0: names · pass1: desc-only */
                char buf[160]; snprintf(buf, sizeof buf, "/%s", g_cmds[i]);
                g_match[g_nmatch] = strdup(buf); g_mdesc[g_nmatch] = strdup(g_cdesc[i] ? g_cdesc[i] : ""); g_nmatch++;
            }
    } else if (tok[0] == '@') {                       /* @file */
        g_menu_kind = '@'; const char *path = tok + 1;
        char dir[1024], base[1024]; const char *slash = strrchr(path, '/');
        if (slash) { size_t dl=(size_t)(slash-path); memcpy(dir,path,dl); dir[dl]=0; snprintf(base,sizeof base,"%s",slash+1); }
        else { strcpy(dir, "."); snprintf(base,sizeof base,"%s",path); }
        DIR *d = opendir(dir[0]?dir:"."); if (d) {
            struct dirent *e; size_t bl = strlen(base);
            while ((e = readdir(d)) && g_nmatch < 256) {
                if (e->d_name[0]=='.' && (base[0]!='.')) continue;
                if (!strncmp(e->d_name, base, bl)) {
                    char buf[2048];
                    if (slash) snprintf(buf,sizeof buf,"@%.*s/%s", (int)(slash-path), path, e->d_name);
                    else snprintf(buf,sizeof buf,"@%s", e->d_name);
                    g_match[g_nmatch] = strdup(buf); g_mdesc[g_nmatch] = strdup(""); g_nmatch++;
                }
            }
            closedir(d);
        }
    }
    g_menu = g_nmatch > 0;
    if (g_msel >= g_nmatch) g_msel = 0;
}
static void menu_accept(void) {
    if (!g_menu || g_nmatch == 0) return;
    const char *comp = g_match[g_msel];
    /* replace [g_tok_start, g_icur) with comp */
    int tail = g_ilen - g_icur; int cl = (int)strlen(comp);
    if (g_tok_start + cl + tail < (int)sizeof g_in - 2) {
        memmove(g_in + g_tok_start + cl, g_in + g_icur, (size_t)tail);
        memcpy(g_in + g_tok_start, comp, (size_t)cl);
        g_ilen = g_tok_start + cl + tail; g_icur = g_tok_start + cl;
        g_in[g_ilen] = 0;
        if (g_menu_kind == '@' && g_in[g_icur-1] != '/') in_insert(" ", 1);   /* space after a file, not a slash cmd or dir */
    }
    menu_clear();
}

/* ====================================================== submit =========== */
/* pasted clipboard images (base64 png), attached to the next submitted message */
static char *g_imgs[8]; static int g_nimg = 0;
static char *g_bash_ctx = NULL; static size_t g_bash_len = 0, g_bash_cap = 0;   /* !bash output queued to ride with the next message */
/* Ctrl+V: read a clipboard image (wayland/x11), base64 it, drop an [Image #N] chip */
static void paste_image(void) {
    if (g_nimg >= 8) return;
    FILE *pp = popen("{ wl-paste --type image/png 2>/dev/null || "
                     "xclip -selection clipboard -t image/png -o 2>/dev/null; } | base64 -w0", "r");
    if (!pp) return;
    char *b = NULL; size_t cap = 0, len = 0, got; char rb[65536];
    while ((got = fread(rb, 1, sizeof rb, pp)) > 0) {
        if (len + got + 1 > cap) { while (len + got + 1 > cap) cap = cap ? cap*2 : 131072; b = realloc(b, cap); }
        memcpy(b + len, rb, got); len += got;
        if (len > 24u*1024*1024) break;
    }
    pclose(pp);
    if (!b || len < 64) { free(b); return; }          /* nothing image-shaped on the clipboard */
    b[len] = 0;
    g_imgs[g_nimg++] = b;
    char chip[24]; snprintf(chip, sizeof chip, "[Image #%d]", g_nimg);
    in_insert(chip, (int)strlen(chip));
}

/* build + send a user-message frame for `text` (plus any pending images) and start a turn.
   Does NOT add a transcript block — submit_input owns that (so queued messages show immediately). */
static void dispatch_user(const char *text) {
    char *combined = NULL;
    if (g_bash_ctx && g_bash_len) {                  /* prepend pending !bash output so the model sees it */
        combined = malloc(g_bash_len + strlen(text) + 1);
        memcpy(combined, g_bash_ctx, g_bash_len); strcpy(combined + g_bash_len, text);
        text = combined;
        free(g_bash_ctx); g_bash_ctx = NULL; g_bash_len = g_bash_cap = 0;
    }
    char *esc = j_escape(text);
    char *msg;
    if (g_nimg == 0) {
        msg = malloc(strlen(esc) + 96);
        sprintf(msg, "{\"type\":\"user\",\"message\":{\"role\":\"user\",\"content\":\"%s\"}}", esc);
    } else {                                          /* array content: text + base64 image blocks */
        size_t tot = strlen(esc) + 160;
        for (int i = 0; i < g_nimg; i++) tot += strlen(g_imgs[i]) + 160;
        msg = malloc(tot); char *w = msg;
        w += sprintf(w, "{\"type\":\"user\",\"message\":{\"role\":\"user\",\"content\":[{\"type\":\"text\",\"text\":\"%s\"}", esc);
        for (int i = 0; i < g_nimg; i++)
            w += sprintf(w, ",{\"type\":\"image\",\"source\":{\"type\":\"base64\",\"media_type\":\"image/png\",\"data\":\"%s\"}}", g_imgs[i]);
        sprintf(w, "]}}");
    }
    send_line(msg); free(msg); free(esc); free(combined);
    for (int i = 0; i < g_nimg; i++) { free(g_imgs[i]); g_imgs[i] = NULL; }
    g_nimg = 0;
    g_busy = true; g_scroll = 0;
    g_turn_start = time(NULL); g_turn_n++; g_think_est = 0; g_turn_bytes = 0;   /* (re)start the spinner */
    snprintf(g_status, sizeof g_status, "requesting");
}
/* ! bash mode: run the command locally (not via the model), render it like a Bash tool + result. */
/* queue a !bash command + its output to ride along with the next user message */
static void bash_ctx_add(const char *cmd, const char *out) {
    char hdr[256]; int hn = snprintf(hdr, sizeof hdr, "Output of running `%s`:\n", cmd);
    if (hn < 0) return;
    if (hn > (int)sizeof hdr - 1) hn = (int)sizeof hdr - 1;
    size_t on = out ? strlen(out) : 0;
    size_t need = g_bash_len + (size_t)hn + on + 3;
    if (need > 65536) return;                         /* cap pending context */
    if (need > g_bash_cap) { while (need > g_bash_cap) g_bash_cap = g_bash_cap ? g_bash_cap*2 : 4096; g_bash_ctx = realloc(g_bash_ctx, g_bash_cap); }
    memcpy(g_bash_ctx + g_bash_len, hdr, (size_t)hn); g_bash_len += (size_t)hn;
    if (on) { memcpy(g_bash_ctx + g_bash_len, out, on); g_bash_len += on; }
    g_bash_ctx[g_bash_len++] = '\n'; g_bash_ctx[g_bash_len++] = '\n';
    g_bash_ctx[g_bash_len] = 0;
}
static void run_bang(const char *cmd) {
    int hb = blk_new(B_TOOL);
    char hdr[16500]; snprintf(hdr, sizeof hdr, "● $ %s", cmd); blk_marked(hb, hdr, 1);
    char full[16500]; snprintf(full, sizeof full, "%s 2>&1", cmd);
    FILE *pp = popen(full, "r");
    int rb = blk_new(B_RESULT);
    if (!pp) { blk_marked(rb, "(failed to run)", 3); return; }
    char buf[8192]; size_t got; char *out = NULL; size_t cap = 0, len = 0;
    while ((got = fread(buf, 1, sizeof buf, pp)) > 0) {
        if (len + got + 1 > cap) { while (len+got+1 > cap) cap = cap?cap*2:8192; out = realloc(out, cap); }
        memcpy(out + len, buf, got); len += got;
    }
    int rc = pclose(pp);
    if (out) { out[len] = 0; truncate_marker(out, 8000); }
    blk_marked(rb, (out && len) ? out : "(no output)", (rc == 0) ? 4 : 3);
    bash_ctx_add(cmd, (out && len) ? out : "(no output)");
    blk_marked(rb, "\xe2\x86\xb3 included with your next message to Claude", 6);   /* ↳ footnote */
    free(out); g_scroll = 0;
}
/* # memory: append a bullet to ./CLAUDE.md and confirm. */
static void add_memory(const char *text) {
    int b = blk_new(B_SYS);
    FILE *f = fopen("CLAUDE.md", "a");
    if (f) { fprintf(f, "- %s\n", text); fclose(f);
        char m[16500]; snprintf(m, sizeof m, "✎ added to ./CLAUDE.md: %s", text); blk_str(b, m); }
    else blk_str(b, "✎ could not write ./CLAUDE.md");
    g_scroll = 0;
}
/* wipe the transcript + per-session counters (shared by /clear and resume). */
/* release a block's wrapped-line cache (Run[] arrays across full capacity, the line array, the arena) */
static void block_free_cache(Block *b) {
    for (int k = 0; k < b->crlcap; k++) free(b->crl[k].r);
    free(b->crl); free(b->carena);
    b->crl = NULL; b->crlcap = b->ncrl = 0;
    b->carena = NULL; b->carcap = b->carn = 0;
    b->cW = -1;
}
static void reset_session_state(void) {
    for (size_t i = 0; i < g_nblk; i++) { free(g_blk[i].t); block_free_cache(&g_blk[i]); }
    free(g_bash_ctx); g_bash_ctx = NULL; g_bash_len = g_bash_cap = 0;   /* drop any pending !bash context */
    g_nblk = 0; g_cur_asst = -1; g_cur_think = -1;
    g_cost = 0; g_dur_ms = 0; g_in_tok = 0; g_out_tok = 0; g_turn_n = 0; g_scroll = 0;
}
/* rebuild the transcript blocks from a stored session .jsonl (resume display). */
static void load_transcript(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) return;
    char *ln = NULL; size_t cap = 0; ssize_t n;
    while ((n = getline(&ln, &cap, f)) > 0) {
        /* stored jsonl puts the top-level "type" AFTER the message object, so match it directly
           (j_str would return the nested message.type "message" / content[].type "text"). */
        bool is_user = strstr(ln, "\"type\":\"user\"") != NULL;
        bool is_asst = !is_user && strstr(ln, "\"type\":\"assistant\"") != NULL;
        if (is_user) {
            char *msg = j_obj(ln, "message");
            char *c = msg ? j_str(msg, "content") : NULL;     /* string content = a typed prompt */
            if (c) { char *u = j_unescape_dup(c); int b = blk_new(B_USER); blk_str(b, u); free(u); free(c); }
            else if (msg) {                                   /* array content = tool_result(s) */
                char *arr = j_arr(msg, "content");
                if (arr && strstr(arr, "tool_result") && strstr(arr, "TodoWrite") == NULL) {
                    char *rc = j_str(arr, "content");
                    if (rc) { char *u = j_unescape_dup(rc);
                        truncate_marker(u, 4000);
                        int b = blk_new(B_RESULT); blk_marked(b, u, 4); free(u); free(rc); }
                }
                free(arr);
            }
            free(msg);
        } else if (is_asst) {
            char *arr = j_arr(ln, "content");                 /* message.content array */
            if (arr) {
                const char *p = arr;
                while ((p = strchr(p, '{')) != NULL) {
                    const char *st = p; const char *q = j_obj_end(p);
                    size_t ol = (size_t)(q - st); char *obj = malloc(ol + 1); memcpy(obj, st, ol); obj[ol] = 0;
                    char *bt = j_str(obj, "type");
                    if (bt && !strcmp(bt, "text")) {
                        const char *tk = strstr(obj, "\"text\":");   /* anchor on the key — the type value is also "text" */
                        char *t = tk ? j_str(tk, "text") : NULL;
                        if (t && *t) { int b = blk_new(B_ASSISTANT); blk_str(b, "⏺ "); blk_unesc(b, t); }
                        free(t);
                    } else if (bt && !strcmp(bt, "tool_use")) {
                        char *nm = j_str(obj, "name"); char *tin = j_obj(obj, "input");
                        int b = blk_new(B_TOOL); render_tool(b, nm ? nm : "tool", tin, false);
                        free(nm); free(tin);
                    }
                    free(bt); free(obj); p = q;
                }
                free(arr);
            }
        }
    }
    free(ln); fclose(f);
}
/* ~/.claude/projects/<cwd-slug> — where this project's session .jsonl files live. */
static void project_dir(char *out, size_t n) {
    char slug[600]; snprintf(slug, sizeof slug, "%s", g_cwd[0] ? g_cwd : ".");
    for (char *p = slug; *p; p++) if (*p == '/') *p = '-';
    snprintf(out, n, "%s/.claude/projects/%s", getenv("HOME") ? getenv("HOME") : "", slug);
}
/* sidecar mapping session-id → custom name (the engine has no native name field). One
   "<id> <name>" line per renamed session, alongside the .jsonl files in the project dir. */
static void names_path(char *out, size_t n) {
    char dir[800]; project_dir(dir, sizeof dir);
    snprintf(out, n, "%s/.crud-names", dir);
}
static void session_name_get(const char *id, char *out, size_t n) {
    out[0] = 0;
    char path[900]; names_path(path, sizeof path);
    FILE *f = fopen(path, "r"); if (!f) return;
    char *ln = NULL; size_t cap = 0; ssize_t r; size_t idl = strlen(id);
    while ((r = getline(&ln, &cap, f)) > 0) {
        if ((size_t)r > idl && !strncmp(ln, id, idl) && ln[idl] == ' ') {
            char *nm = ln + idl + 1; size_t L = strlen(nm);
            while (L && (nm[L-1]=='\n' || nm[L-1]=='\r')) nm[--L] = 0;
            snprintf(out, n, "%s", nm); break;
        }
    }
    free(ln); fclose(f);
}
static void session_name_set(const char *id, const char *name) {
    char path[900]; names_path(path, sizeof path);
    char *lines[128]; int nl = 0; size_t idl = strlen(id);
    FILE *f = fopen(path, "r");                       /* keep every line except this id's */
    if (f) { char *ln = NULL; size_t cap = 0; ssize_t r;
        while ((r = getline(&ln, &cap, f)) > 0 && nl < 128) {
            bool match = ((size_t)r > idl && !strncmp(ln, id, idl) && ln[idl] == ' ');
            if (!match) { while (r > 0 && (ln[r-1]=='\n' || ln[r-1]=='\r')) ln[--r] = 0;
                          if (r > 0) lines[nl++] = strdup(ln); }
        }
        free(ln); fclose(f);
    }
    FILE *w = fopen(path, "w");
    if (w) {
        for (int i = 0; i < nl; i++) fprintf(w, "%s\n", lines[i]);
        fprintf(w, "%s ", id);
        for (const char *c = name; *c; c++) fputc((*c=='\n' || *c=='\r') ? ' ' : *c, w);
        fputc('\n', w);
        fclose(w);
    }
    for (int i = 0; i < nl; i++) free(lines[i]);
}
/* list this project's stored sessions (newest first) for the resume picker. */
static void populate_sessions(void) {
    g_nsess = 0; g_ssel = 0;
    char dir[800]; project_dir(dir, sizeof dir);
    DIR *d = opendir(dir); if (!d) return;
    struct dirent *e;
    while ((e = readdir(d)) != NULL && g_nsess < 64) {
        size_t L = strlen(e->d_name);
        if (L < 7 || strcmp(e->d_name + L - 6, ".jsonl")) continue;
        Sess *s = &g_sess[g_nsess];
        snprintf(s->path, sizeof s->path, "%s/%s", dir, e->d_name);
        snprintf(s->id, sizeof s->id, "%.*s", (int)(L - 6), e->d_name);
        struct stat stt; s->mtime = (stat(s->path, &stt) == 0) ? (long)stt.st_mtime : 0;
        s->label[0] = 0;
        FILE *f = fopen(s->path, "r");
        if (f) { char *ln = NULL; size_t cap = 0; ssize_t n;
            while ((n = getline(&ln, &cap, f)) > 0) {
                if (!strstr(ln, "\"type\":\"user\"")) continue;
                char *msg = j_obj(ln, "message"); char *c = msg ? j_str(msg, "content") : NULL;
                bool got = false;
                if (c) {                                  /* skip synthetic <…> meta lines; want the first real prompt */
                    char *u = j_unescape_dup(c);
                    const char *p = u; while (*p == ' ' || *p == '\n' || *p == '\t') p++;
                    if (*p && *p != '<') { snprintf(s->label, sizeof s->label, "%.130s", p); got = true; }
                    free(u);
                }
                free(c); free(msg);
                if (got) break;
            }
            free(ln); fclose(f);
        }
        if (!s->label[0]) snprintf(s->label, sizeof s->label, "(no prompt)");
        for (char *p = s->label; *p; p++) if (*p == '\n' || *p == '\t') *p = ' ';
        session_name_get(s->id, s->name, sizeof s->name);    /* custom name overrides the prompt preview */
        g_nsess++;
    }
    closedir(d);
    for (int i = 1; i < g_nsess; i++) {          /* insertion sort, newest mtime first */
        Sess t = g_sess[i]; int j = i - 1;
        while (j >= 0 && g_sess[j].mtime < t.mtime) { g_sess[j+1] = g_sess[j]; j--; }
        g_sess[j+1] = t;
    }
}
/* resume the selected session: reload its transcript and respawn the engine with --resume. */
static void resume_session(int idx, bool forked) {
    if (idx < 0 || idx >= g_nsess) return;
    Sess *s = &g_sess[idx];
    reset_session_state();
    load_transcript(s->path);
    restart_engine(s->id, forked);
    snprintf(g_session, sizeof g_session, "%.8s", s->id);
    int b = blk_new(B_SYS); char m[80];
    snprintf(m, sizeof m, forked ? "✦ forked from session %.8s" : "✦ resumed session %.8s", s->id);
    blk_str(b, m);
    g_resume_open = false; g_scroll = 0;
}

/* ---- generic choice picker (model / effort / rewind) ---- */
static void choice_add(const char *label, int ref) {
    if (g_nchoice >= 24) return;
    snprintf(g_choice[g_nchoice], sizeof g_choice[0], "%s", label);
    g_choice_ref[g_nchoice] = ref; g_nchoice++;
}
/* swap the engine's model/effort in-place: same session (resume g_sid), new flag. */
static bool valid_model(const char *v) {
    static const char *ok[] = {"default","opus","sonnet","haiku","opus[1m]","sonnet[1m]","opusplan"};
    for (size_t i = 0; i < sizeof ok/sizeof ok[0]; i++) if (!strcmp(v, ok[i])) return true;
    return !strncmp(v, "claude", 6);                 /* also allow a full model id */
}
static bool valid_effort(const char *v) {
    static const char *ok[] = {"low","medium","high","xhigh","max"};
    for (size_t i = 0; i < sizeof ok/sizeof ok[0]; i++) if (!strcmp(v, ok[i])) return true;
    return false;
}
static void apply_model(const char *v) {
    snprintf(g_model_arg, sizeof g_model_arg, "%s", strcmp(v, "default") ? v : "");
    snprintf(g_model, sizeof g_model, "%s", v);      /* optimistic header update; next system/init refines it */
    restart_engine(g_sid[0] ? g_sid : NULL, false);
    int b = blk_new(B_SYS); char m[80]; snprintf(m, sizeof m, "✦ model → %s", v); blk_str(b, m); g_scroll = 0;
}
static void apply_effort(const char *v) {
    snprintf(g_effort, sizeof g_effort, "%s", v);
    restart_engine(g_sid[0] ? g_sid : NULL, false);
    int b = blk_new(B_SYS); char m[80]; snprintf(m, sizeof m, "✦ effort → %s", v); blk_str(b, m); g_scroll = 0;
}
static void choice_apply(void) {
    if (g_chsel < 0 || g_chsel >= g_nchoice) { g_choice_open = false; return; }
    char kind = g_choice_kind; const char *v = g_choice[g_chsel]; int ref = g_choice_ref[g_chsel];
    g_choice_open = false;
    if (kind == 'm') apply_model(v);
    else if (kind == 'e') apply_effort(v);
    else if (kind == 'r') { if (ref >= 0 && ref < g_histn) in_set(g_hist[ref]); }  /* rewind: reload prompt */
}
/* ---- /mcp · /agents · /login viewers (read-only info blocks) ---- */
static void show_mcp(void) {
    int b = blk_new(B_SYS); blk_str(b, "MCP servers");
    int n = 0;
    if (g_mcp) {                                      /* parse mcp_servers: [{"name":…,"status":…}] */
        const char *p = g_mcp;
        while ((p = strchr(p, '{')) != NULL) {
            const char *st = p; const char *q = j_obj_end(p);
            size_t ol = (size_t)(q - st); char *obj = malloc(ol + 1); memcpy(obj, st, ol); obj[ol] = 0;
            char *nm = j_str(obj, "name"); char *stt = j_str(obj, "status");
            char line[160]; snprintf(line, sizeof line, "  • %s%s%s", nm ? nm : "?", stt ? " — " : "", stt ? stt : "");
            blk_str(b, "\n"); blk_str(b, line); n++;
            free(nm); free(stt); free(obj); p = q;
        }
    }
    if (!n) blk_str(b, "\n  (none configured — add via ~/.claude/settings.json or .mcp.json)");
    g_scroll = 0;
}
static void list_agent_dir(int b, const char *dir, int *n) {
    DIR *d = opendir(dir); if (!d) return; struct dirent *e;
    while ((e = readdir(d)) != NULL) {
        size_t L = strlen(e->d_name);
        if (L < 4 || strcmp(e->d_name + L - 3, ".md")) continue;
        char line[160]; snprintf(line, sizeof line, "  • %.*s", (int)(L - 3), e->d_name);
        blk_str(b, "\n"); blk_str(b, line); (*n)++;
    }
    closedir(d);
}
static void show_agents(void) {
    int b = blk_new(B_SYS); blk_str(b, "Agents"); int n = 0;
    const char *home = getenv("HOME");
    if (home) { char p[320]; snprintf(p, sizeof p, "%s/.claude/agents", home); list_agent_dir(b, p, &n); }
    list_agent_dir(b, ".claude/agents", &n);
    if (!n) blk_str(b, "\n  (no custom agents — subagents still run via the Task tool)");
    g_scroll = 0;
}
static void show_login(void) {
    int b = blk_new(B_SYS);
    const char *home = getenv("HOME"); char path[320]; path[0] = 0;
    if (home) snprintf(path, sizeof path, "%s/.claude/.credentials.json", home);
    FILE *f = path[0] ? fopen(path, "rb") : NULL;
    if (!f) { blk_str(b, "Not logged in — run `claude` in a terminal to authenticate"); g_scroll = 0; return; }
    char buf[16384]; size_t nn = fread(buf, 1, sizeof buf - 1, f); buf[nn] = 0; fclose(f);
    char *sub = j_str(buf, "subscriptionType"); double exp = j_num(buf, "expiresAt");
    char line[256];
    if (exp > 0) {
        time_t t = (time_t)(exp / 1000.0); struct tm tm; gmtime_r(&t, &tm);
        char when[40]; strftime(when, sizeof when, "%Y-%m-%d %H:%M UTC", &tm);
        snprintf(line, sizeof line, "Logged in · %s · token valid until %s", sub ? sub : "?", when);
    } else snprintf(line, sizeof line, "Logged in · %s", sub ? sub : "?");
    blk_str(b, line); free(sub); g_scroll = 0;
}
/* client-side slash commands (the headless engine can't run the interactive ones). true = handled. */
/* 20-cell █/░ progress bar for a 0..1 fraction, into a plain-text buffer (used by /usage) */
static void usage_bar(char *o, size_t cap, double frac) {
    if (frac < 0) frac = 0;
    if (frac > 1) frac = 1;
    int fill = (int)(frac * 20 + 0.5); size_t left = cap; char *w = o;
    for (int i = 0; i < 20 && left > 4; i++) {
        const char *cell = (i < fill) ? "\xe2\x96\x88" : "\xe2\x96\x91";   /* █ filled · ░ empty */
        int n = snprintf(w, left, "%s", cell); if (n <= 0) break; w += n; left -= (size_t)n;
    }
}
/* /context — context-window fill from the live token counter (we only have the total, not the
   per-category breakdown the real TUI shows, so render used / max with a bar). */
static void show_context(void) {
    int b = blk_new(B_SYS);
    long maxctx = strstr(g_model, "1m") ? 1000000 : 200000;
    double used = g_in_tok > 0 ? g_in_tok : 0;
    double frac = maxctx > 0 ? used / (double)maxctx : 0;
    char bar[80]; usage_bar(bar, sizeof bar, frac);
    char uk[16], mk[16], fk[16]; fmt_k(uk, used); fmt_k(mk, (double)maxctx);
    double freed = (double)maxctx - used; if (freed < 0) freed = 0; fmt_k(fk, freed);
    char m[256];
    snprintf(m, sizeof m, "Context usage\n  %s  %s / %s  (%d%%)\n  %s tokens free",
        bar, uk, mk, (int)(frac*100 + 0.5), fk);
    blk_str(b, m); g_scroll = 0;
}
/* /diff — working-tree changes via git, shown in a fenced code block (B_SYS doesn't collapse). */
static void show_diff(void) {
    int b = blk_new(B_SYS);
    FILE *pp = popen("git --no-pager diff --color=never 2>&1", "r");
    if (!pp) { blk_str(b, "could not run git"); g_scroll = 0; return; }
    char buf[8192]; size_t got, cap = 0, len = 0; char *out = NULL;
    while ((got = fread(buf, 1, sizeof buf, pp)) > 0) {
        if (len + got + 1 > cap) { while (len+got+1 > cap) cap = cap?cap*2:8192; out = realloc(out, cap); }
        memcpy(out + len, buf, got); len += got;
    }
    int rc = pclose(pp);
    if (!out || len == 0) { blk_str(b, rc == 0 ? "\xe2\x9c\xa6 no uncommitted changes" : "not a git repository"); free(out); g_scroll = 0; return; }
    out[len] = 0; truncate_marker(out, 16000);
    blk_str(b, "Working tree changes\n```\n"); blk_str(b, out);
    if (out[strlen(out)-1] != '\n') blk_str(b, "\n");
    blk_str(b, "```");
    free(out); g_scroll = 0;
}
/* /export — write the whole transcript to ./crud-export-<stamp>.md, marker bytes stripped. */
static void export_conversation(void) {
    int b = blk_new(B_SYS);
    time_t t = time(NULL); struct tm tm; localtime_r(&t, &tm);
    char fname[96]; strftime(fname, sizeof fname, "crud-export-%Y%m%d-%H%M%S.md", &tm);
    FILE *f = fopen(fname, "w");
    if (!f) { blk_str(b, "could not write export file"); g_scroll = 0; return; }
    char when[40]; strftime(when, sizeof when, "%Y-%m-%d %H:%M", &tm);
    fprintf(f, "# Conversation export\n\n- exported: %s\n", when);
    if (g_model[0]) fprintf(f, "- model: %s\n", g_model);
    if (g_sid[0])   fprintf(f, "- session: %s\n", g_sid);
    fprintf(f, "\n");
    int n = 0;
    for (size_t i = 0; i < g_nblk; i++) {
        Block *bl = &g_blk[i];
        if (!bl->t || bl->len == 0) continue;
        const char *role = bl->kind==B_USER?"User":bl->kind==B_ASSISTANT?"Claude":
                           bl->kind==B_THINKING?"Claude (thinking)":bl->kind==B_TOOL?"Tool":
                           bl->kind==B_RESULT?"Result":"System";
        bool code = (bl->kind == B_TOOL || bl->kind == B_RESULT);
        fprintf(f, "## %s\n\n", role);
        if (code) fprintf(f, "```\n");
        const char *p = bl->t, *end = bl->t + bl->len;
        while (p < end) {
            const char *nl = memchr(p, '\n', (size_t)(end - p)); const char *le = nl ? nl : end;
            const char *txt = (*p >= 1 && *p <= 9) ? p + 1 : p;      /* drop a leading marker byte */
            if (le > txt) fwrite(txt, 1, (size_t)(le - txt), f);
            fputc('\n', f);
            if (!nl) break;
            p = nl + 1;
        }
        if (code) fprintf(f, "```\n");
        fprintf(f, "\n"); n++;
    }
    fclose(f);
    char m[256]; snprintf(m, sizeof m, "\xe2\x9c\xa6 exported %d blocks to ./%s", n, fname);
    blk_str(b, m); g_scroll = 0;
}
static bool handle_client_command(const char *line) {
    while (*line == ' ') line++;
    char cmd[64]; int ci = 0;                        /* first token only — autocomplete adds a trailing space */
    while (line[ci] && line[ci] != ' ' && line[ci] != '\n' && ci < 63) { cmd[ci] = line[ci]; ci++; }
    cmd[ci] = 0;
    if (!strcmp(cmd, "/clear")) {                    /* fresh session: wipe transcript + respawn engine */
        reset_session_state(); restart_engine(NULL, false);
        int b = blk_new(B_SYS); blk_str(b, "✦ started a fresh session"); return true;
    }
    if (!strcmp(cmd, "/resume") || !strcmp(cmd, "/sessions")) {
        populate_sessions();
        if (g_nsess == 0) { int b = blk_new(B_SYS); blk_str(b, "no saved sessions for this project"); return true; }
        const char *ra = line + ci; while (*ra == ' ') ra++;       /* "/resume <name|id>" → resume directly, no picker */
        if (*ra) {
            int hit = -1;
            for (int i = 0; i < g_nsess; i++)                       /* prefer exact custom-name, then id-prefix, then name-substring */
                if (g_sess[i].name[0] && !strcasecmp(g_sess[i].name, ra)) { hit = i; break; }
            if (hit < 0) for (int i = 0; i < g_nsess; i++) if (!strncmp(g_sess[i].id, ra, strlen(ra))) { hit = i; break; }
            if (hit < 0) for (int i = 0; i < g_nsess; i++) if (g_sess[i].name[0] && ci_strstr(g_sess[i].name, ra)) { hit = i; break; }
            if (hit >= 0) { resume_session(hit, false); return true; }
            int b = blk_new(B_SYS); char m[160]; snprintf(m, sizeof m, "no session named or starting with '%.60s'", ra); blk_str(b, m); return true;
        }
        g_resume_open = true; g_ssel = 0; return true;
    }
    if (!strcmp(cmd, "/rename")) {                     /* name the current session (sidecar; engine has no name field) */
        const char *ra = line + ci; while (*ra == ' ') ra++;
        if (!g_sid[0]) { int b = blk_new(B_SYS); blk_str(b, "no active session yet — send a message first, then /rename <name>"); return true; }
        if (!*ra)      { int b = blk_new(B_SYS); blk_str(b, "usage: /rename <name>"); return true; }
        session_name_set(g_sid, ra);
        int b = blk_new(B_SYS); char m[200]; snprintf(m, sizeof m, "\xe2\x9c\xa6 renamed this session to \xe2\x80\x9c%.150s\xe2\x80\x9d", ra);
        blk_str(b, m); g_scroll = 0; return true;
    }
    if (!strcmp(cmd, "/copy")) {                       /* copy Claude's last response (even if scrolled off) */
        int bi = -1;
        for (int i = (int)g_nblk - 1; i >= 0; i--) if (g_blk[i].kind == B_ASSISTANT) { bi = i; break; }
        if (bi < 0 || !g_blk[bi].t || g_blk[bi].len == 0) { int b = blk_new(B_SYS); blk_str(b, "no response to copy yet"); return true; }
        const char *t = g_blk[bi].t; int len = (int)g_blk[bi].len;
        if (len >= 4 && (unsigned char)t[0] == 0xE2 && t[3] == ' ') { t += 4; len -= 4; }   /* drop the leading ⏺/✻ marker */
        clipboard_copy(t, len);
        snprintf(g_toast, sizeof g_toast, "✓ copied last response (%d chars)", len);
        g_toast_until = now_ms() + 1500;
        return true;
    }
    if (!strcmp(cmd, "/branch") || !strcmp(cmd, "/fork")) {   /* fork the CURRENT conversation into a new session */
        if (!g_sid[0]) { int b = blk_new(B_SYS); blk_str(b, "no active session to branch from yet"); return true; }
        restart_engine(g_sid, true);                          /* --resume <current> --fork-session; transcript kept */
        int b = blk_new(B_SYS); char m[96];
        snprintf(m, sizeof m, "✦ branched from %.8s — continuing in a new session", g_sid);
        blk_str(b, m); g_scroll = 0; return true;
    }
    if (!strcmp(cmd, "/memory")) {                    /* memory editing is a TUI editor; point at the # shortcut */
        int b = blk_new(B_SYS);
        blk_str(b, "Memory editing is interactive. In crud-cli, type `#your note` to append a bullet to ./CLAUDE.md, or edit the memory files directly.");
        return true;
    }
    if (!strcmp(cmd, "/config") || !strcmp(cmd, "/statusline") ||
        !strcmp(cmd, "/output-style") || !strcmp(cmd, "/install-github-app") ||
        !strcmp(cmd, "/permissions") || !strcmp(cmd, "/hooks") || !strcmp(cmd, "/keybindings") ||
        !strcmp(cmd, "/terminal-setup") || !strcmp(cmd, "/tasks") ||
        !strcmp(cmd, "/release-notes") || !strcmp(cmd, "/remote-env") || !strcmp(cmd, "/reload-plugins") ||
        !strcmp(cmd, "/feedback") || !strcmp(cmd, "/doctor") || !strcmp(cmd, "/logout") ||
        !strcmp(cmd, "/privacy-settings")) {   /* interactive — can't host in a headless wrapper */
        int b = blk_new(B_SYS); char m[220];
        snprintf(m, sizeof m, "%s is interactive — not hosted by this frontend. Run the standard `claude` CLI for it, or edit ~/.claude/settings.json directly.", cmd);
        blk_str(b, m); return true;
    }
    const char *arg = line + ci; while (*arg == ' ') arg++;   /* argument after the command, if any */
    if (!strcmp(cmd, "/model")) {                     /* "/model sonnet" → direct; "/model" → picker */
        if (*arg) {
            if (valid_model(arg)) apply_model(arg);
            else { int b = blk_new(B_SYS); char m[160]; snprintf(m, sizeof m, "unknown model '%.40s' (try: default opus sonnet haiku opus[1m] sonnet[1m] opusplan)", arg); blk_str(b, m); }
            return true;
        }
        g_choice_kind = 'm'; g_nchoice = 0; g_chsel = 0; snprintf(g_choice_title, sizeof g_choice_title, "model");
        const char *ms[] = { "default", "opus", "sonnet", "haiku", "opus[1m]", "sonnet[1m]", "opusplan" };
        for (size_t i = 0; i < sizeof ms/sizeof ms[0]; i++) { choice_add(ms[i], 0); if (!strcmp(ms[i], g_model_arg[0]?g_model_arg:"default")) g_chsel = (int)i; }
        g_choice_open = true; return true;
    }
    if (!strcmp(cmd, "/effort")) {                    /* "/effort high" → direct; "/effort" → picker */
        if (*arg) {
            if (valid_effort(arg)) apply_effort(arg);
            else { int b = blk_new(B_SYS); char m[100]; snprintf(m, sizeof m, "unknown effort '%.40s' (low medium high xhigh max)", arg); blk_str(b, m); }
            return true;
        }
        g_choice_kind = 'e'; g_nchoice = 0; g_chsel = 0; snprintf(g_choice_title, sizeof g_choice_title, "effort");
        const char *es[] = { "low", "medium", "high", "xhigh", "max" };
        for (size_t i = 0; i < sizeof es/sizeof es[0]; i++) { choice_add(es[i], 0); if (!strcmp(es[i], g_effort)) g_chsel = (int)i; }
        g_choice_open = true; return true;
    }
    if (!strcmp(cmd, "/rewind")) {                    /* pick an earlier prompt this session to edit & resend */
        if (g_histn == 0) { int b = blk_new(B_SYS); blk_str(b, "nothing to rewind to yet"); return true; }
        g_choice_kind = 'r'; g_nchoice = 0; snprintf(g_choice_title, sizeof g_choice_title, "rewind");
        for (int i = g_histn - 1; i >= 0 && g_nchoice < 24; i--) choice_add(g_hist[i], i);  /* newest first */
        g_chsel = 0; g_choice_open = true; return true;
    }
    if (!strcmp(cmd, "/mcp"))    { show_mcp();    return true; }
    if (!strcmp(cmd, "/agents")) { show_agents(); return true; }
    if (!strcmp(cmd, "/login") || !strcmp(cmd, "/status")) { show_login(); return true; }
    if (!strcmp(cmd, "/vim")) {                      /* toggle modal (vim) editing */
        g_vim = !g_vim; g_vins = true; g_vop = 0;
        int b = blk_new(B_SYS);
        blk_str(b, g_vim ? "✦ vim mode ON — esc → normal, i/a/o → insert" : "✦ vim mode OFF");
        return true;
    }
    if (!strcmp(cmd, "/usage")) {                     /* plan limits from the usage poller (same data as the header) */
        int b = blk_new(B_SYS); char m[512]; int o = 0;
        o += snprintf(m+o, sizeof m-(size_t)o, "Plan usage");
        if (g_u5 < 0 && g_u7 < 0) {
            snprintf(m+o, sizeof m-(size_t)o, "\n  fetching usage data\xe2\x80\xa6 try again in a moment");
        } else {
            if (g_u5 >= 0) { char bar[80], r[24]; usage_bar(bar, sizeof bar, g_u5/100.0); fmt_reset(r, g_u5r);
                o += snprintf(m+o, sizeof m-(size_t)o, "\n  session (5h)  %s  %d%%%s%s", bar, (int)(g_u5+0.5), r[0]?"   resets in ":"", r); }
            if (g_u7 >= 0) { char bar[80], r[24]; usage_bar(bar, sizeof bar, g_u7/100.0); fmt_reset(r, g_u7r);
                o += snprintf(m+o, sizeof m-(size_t)o, "\n  week (7d)     %s  %d%%%s%s", bar, (int)(g_u7+0.5), r[0]?"   resets in ":"", r); }
        }
        blk_str(b, m); g_scroll = 0; return true;
    }
    if (!strcmp(cmd, "/context")) { show_context(); return true; }
    if (!strcmp(cmd, "/diff"))    { show_diff();    return true; }
    if (!strcmp(cmd, "/export"))  { export_conversation(); return true; }
    if (!strcmp(cmd, "/plan")) {                      /* enter plan mode (same as shift+tab → plan) */
        set_mode("plan"); int b = blk_new(B_SYS);
        blk_str(b, "\xe2\x9c\xa6 plan mode on — Claude proposes a plan before editing (shift+tab cycles modes)");
        g_scroll = 0; return true;
    }
    if (!strcmp(cmd, "/cost")) {
        int b = blk_new(B_SYS); long s = (long)(g_dur_ms / 1000);
        char m[512]; snprintf(m, sizeof m,
            "Session cost\n  total:    $%.4f\n  duration: %ldm %02lds (wall)\n"
            "  tokens:   %.0f in (ctx) · %.0f out (session)\n  turns:    %d",
            g_cost, s/60, s%60, g_in_tok, g_out_tok, g_turn_n);
        blk_str(b, m); g_scroll = 0; return true;
    }
    if (!strcmp(cmd, "/help")) {
        int b = blk_new(B_SYS);
        blk_str(b,
            "crud-cli — keys & modes\n"
            "  enter        send    ·   shift+enter / \\+enter   newline\n"
            "  esc          stop the turn / clear the draft\n"
            "  shift+tab    cycle permission mode (default · accept-edits · plan)\n"
            "  ctrl+o       expand / collapse tool output\n"
            "  ctrl+v       paste a clipboard image\n"
            "  ctrl+c       clear the draft / stop the turn · on an empty prompt, confirm to exit\n"
            "  ↑/↓          history    ·   pgup/pgdn   scroll transcript\n"
            "  /            commands   ·   @           files\n"
            "  !cmd         run a shell command locally\n"
            "  #note        append a memory to ./CLAUDE.md\n"
            "  /cost        session cost & token summary\n"
            "  /rename name name this session   ·   /resume [name]  reopen one (by name)\n"
            "  /resume      reopen an earlier session   ·   /clear  fresh session\n"
            "  start: crud-cli -c (most recent) · crud-cli -r [name] (resume named)\n"
            "  /compact     compact the context (engine)");
        g_scroll = 0; return true;
    }
    return false;
}
static void submit_input(void) {
    if (g_ilen == 0 && g_nimg == 0) return;
    g_in[g_ilen] = 0;
    if (g_in[0] == '/')                              /* trim the trailing space autocomplete adds, so /cmd reaches its handler/engine clean */
        while (g_ilen > 0 && (g_in[g_ilen-1] == ' ' || g_in[g_ilen-1] == '\t')) g_in[--g_ilen] = 0;
    const char *t = g_in; while (*t == ' ') t++;     /* typed quit -> confirmation modal, don't send */
    char tk[16]; int ti = 0;                          /* first token (autocomplete adds a trailing space) */
    while (t[ti] && t[ti] != ' ' && t[ti] != '\n' && ti < 15) { tk[ti] = t[ti]; ti++; }
    tk[ti] = 0;
    if (!strcmp(tk,"/quit")||!strcmp(tk,"/exit")||!strcmp(tk,"quit")||!strcmp(tk,"exit")) {
        in_clear(); menu_clear(); g_confirm_quit = true; g_qsel = 0; return; }
    if (g_in[0] == '!' && g_ilen > 1) { run_bang(g_in + 1); in_clear(); menu_clear(); return; }   /* ! bash */
    if (g_in[0] == '#' && g_ilen > 1) { add_memory(g_in + 1); in_clear(); menu_clear(); return; } /* # memory */
    if (g_in[0] == '/' && handle_client_command(g_in)) { in_clear(); menu_clear(); return; }       /* client cmds */

    int b = blk_new(B_USER);
    if (g_ilen) blk_raw(b, g_in, (size_t)g_ilen);
    if (g_nimg) { char note[40]; snprintf(note, sizeof note, "%s[%d image%s]", g_ilen?"  ":"", g_nimg, g_nimg>1?"s":""); blk_str(b, note); }
    if (g_ilen && g_histn < 256 && (g_histn == 0 || strcmp(g_hist[g_histn-1], g_in)))
        g_hist[g_histn++] = strdup(g_in);
    g_histpos = g_histn;

    if (g_busy) {                                    /* a turn is running — queue and send on turn end */
        if (g_nqueue < 16) { g_queue_blk[g_nqueue] = b; g_queue[g_nqueue++] = strdup(g_in); g_blk[b].queued = true; g_blk[b].ver++; }
        for (int i = 0; i < g_nimg; i++) { free(g_imgs[i]); g_imgs[i] = NULL; } g_nimg = 0;
        in_clear(); menu_clear(); return;
    }
    dispatch_user(g_in);
    in_clear(); menu_clear();
}

/* ====================================================== render =========== */
/* monotonic milliseconds — drives the spinner off the wall clock, not the render rate */
static long now_ms(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (long)ts.tv_sec*1000 + ts.tv_nsec/1000000; }
/* (Re)wrap a block into its own cache, keyed by (ver,W,limit). Cache hits do zero work, so a
   spinner tick / streaming chunk only re-wraps the block that changed, not the whole transcript.
   The emitters write through the g_rl/g_arena scratch globals, so we point those at the block's
   cache buffers for the duration of the emit, then hand the grown buffers back to the block. */
static void block_layout(Block *b, int W, int limit) {
    if (b->cW == W && b->cver == (int)b->ver && b->climit == limit) return;   /* cache hit */
    RLine *srl = g_rl; int snrl = g_nrl, srlcap = g_rlcap;                    /* save scratch */
    char *sar = g_arena; int sarn = g_arn, sarcap = g_arcap;
    g_rl = b->crl; g_rlcap = b->crlcap; g_nrl = 0;                            /* reuse the block's buffers */
    g_arena = b->carena; g_arcap = b->carcap; g_arn = 0;
    if (b->kind == B_TOOL || b->kind == B_RESULT) emit_marked(b, W, limit);
    else emit_markdown(b, W);
    b->crl = g_rl; b->crlcap = g_rlcap; b->ncrl = g_nrl;                      /* take ownership back */
    b->carena = g_arena; b->carcap = g_arcap; b->carn = g_arn;
    for (int k = 0; k < b->ncrl; k++) b->crl[k].abase = b->carena;            /* arena may have moved: set after emit */
    b->cW = W; b->cver = (int)b->ver; b->climit = limit;
    g_rl = srl; g_nrl = snrl; g_rlcap = srlcap;                              /* restore scratch */
    g_arena = sar; g_arn = sarn; g_arcap = sarcap;
}
#define SEL_BG 0x33455f                                 /* text-selection highlight background */
/* This renderer treats one UTF-8 character as one display cell (same model the input cursor uses),
   so selection columns are CHARACTER indices, not byte offsets — otherwise multibyte glyphs (e.g. the
   3-byte "—") would shift the text at a split point. */
static int rl_chars(const char *s, int n) {             /* number of characters in n bytes */
    int c = 0;
    for (int b = 0; b < n; c++) { unsigned char ch=(unsigned char)s[b]; int cl=(ch>=0xF0)?4:(ch>=0xE0)?3:(ch>=0xC0)?2:1; if (b+cl>n) cl=1; b+=cl; }
    return c;
}
static int rl_char_byte(const char *s, int n, int nchars) {  /* byte offset after skipping nchars characters */
    int b = 0;
    while (b < n && nchars > 0) { unsigned char ch=(unsigned char)s[b]; int cl=(ch>=0xF0)?4:(ch>=0xE0)?3:(ch>=0xC0)?2:1; if (b+cl>n) cl=1; b+=cl; nchars--; }
    return b;
}
static int rline_width(const RLine *l) {                /* total display cells (= characters) */
    int w = 0;
    for (int i = 0; i < l->n; i++) w += rl_chars(l->abase + l->r[i].off, l->r[i].len);
    return w;
}
/* draw one wrapped line left-to-right from column 0 (notcurses advances the cursor by true glyph
   width, so the text can never drift); cells in CHARACTER range [sel0,sel1) get the selection bg. */
static void draw_runs(int row, const RLine *l, int sel0, int sel1) {
    ncplane_cursor_move_yx(g_std, row, 0);
    int cc = 0;                                         /* character column at the start of this run */
    for (int i = 0; i < l->n; i++) {
        Run *r = &l->r[i]; Sty s = r->s; const char *txt = l->abase + r->off;
        uint16_t st = NCSTYLE_NONE; if (s.bold) st |= NCSTYLE_BOLD; if (s.ital||s.dim) st |= NCSTYLE_ITALIC;
        ncplane_set_styles(g_std, st);
        ncplane_set_fg_rgb(g_std, s.fg);
        int rc = rl_chars(txt, r->len);                 /* characters in this run */
        int a = sel0 - cc; if (a < 0) a = 0; if (a > rc) a = rc;   /* selection start within run (chars) */
        int b = sel1 - cc; if (b < 0) b = 0; if (b > rc) b = rc;   /* selection end within run (chars) */
        int ba = rl_char_byte(txt, r->len, a), bb = rl_char_byte(txt, r->len, b);
        int seg[3][2] = { {0,ba}, {ba,bb}, {bb,r->len} };          /* before-sel | in-sel | after-sel (bytes) */
        for (int p = 0; p < 3; p++) {
            int c0 = seg[p][0], c1 = seg[p][1]; if (c1 <= c0) continue;
            if (p == 1) ncplane_set_bg_rgb(g_std, SEL_BG);
            else if (s.has_bg) ncplane_set_bg_rgb(g_std, s.bg);
            else ncplane_set_bg_default(g_std);
            ncplane_putnstr(g_std, (size_t)(c1 - c0), txt + c0);
        }
        cc += rc;
    }
    ncplane_set_styles(g_std, NCSTYLE_NONE); ncplane_set_bg_default(g_std);
}

static void fmt_k(char *o, double n) {
    if (n >= 1000) snprintf(o, 16, "%.1fk", n / 1000.0); else snprintf(o, 16, "%.0f", n);
}
static const char *spin_word(void) {                 /* whimsical gerund, one per turn */
    static const char *W[] = {"Baking","Churning","Cooking","Brewing","Crafting","Conjuring",
        "Pondering","Noodling","Whirring","Computing","Tinkering","Simmering","Percolating","Marinating"};
    return W[g_turn_n % 14];
}
/* solid progress bar at (row,x), w cells, fraction f: filled cells colored, rest very dark */
static void draw_bar(int row, int x, int w, double f, uint32_t fill) {
    if (f < 0) f = 0;
    if (f > 1) f = 1;
    int full = (int)(f * w + 0.5);
    for (int i = 0; i < w; i++) {
        ncplane_set_fg_rgb(g_std, i < full ? fill : 0x2b3138);
        ncplane_putstr_yx(g_std, row, x + i, "█");
    }
}
static int dwidth(const char *s) {              /* display width (utf8 lead bytes) */
    int w = 0; for (const unsigned char *p=(const unsigned char*)s; *p; p++) if ((*p & 0xC0) != 0x80) w++;
    return w;
}
static uint32_t ucol(double pct) { return pct > 85 ? 0xf38ba8 : pct > 60 ? COL_WARN : COL_OK; }
static void fmt_reset(char *o, long reset) {     /* "4h" / "4d" / "" */
    o[0] = 0; long rem = reset ? reset - (long)time(NULL) : 0;
    if (reset && rem > 0) { if (rem >= 86400) snprintf(o, 24, "%ldd", rem/86400);
                            else snprintf(o, 24, "%ldh", (rem + 3599)/3600); }
}
/* one aligned usage row in a fixed panel: label (left) · bar (fixed x/width) · value (right-aligned) */
#define UBARW 14
static void usage_row(int row, int px, int panelW, const char *label, double frac, const char *val, const char *reset) {
    ncplane_set_bg_default(g_std);
    ncplane_set_fg_rgb(g_std, 0xb2b8c2); ncplane_putstr_yx(g_std, row, px, label);
    draw_bar(row, px + 4, UBARW, frac, ucol(frac * 100));
    int rl = reset && reset[0] ? dwidth(reset) + 3 : 0;
    int vx = px + panelW - dwidth(val) - rl;
    ncplane_set_fg_rgb(g_std, 0xdadada); ncplane_putstr_yx(g_std, row, vx, val);
    if (rl) { ncplane_set_fg_rgb(g_std, 0x7a828c); ncplane_putstr_yx(g_std, row, vx + dwidth(val), " · ");
        ncplane_set_fg_rgb(g_std, 0xe0a35a); ncplane_putstr_yx(g_std, row, vx + dwidth(val) + 3, reset); }
}
/* palette word-wrap: bytes of `s` (len) that fit in `width` cols, breaking at the last space when
   possible. *consume = bytes to advance (skips the break space). ASCII-oriented (descriptions). */
static int pal_wrap(const char *s, int len, int width, int *consume) {
    if (len <= width) { *consume = len; return len; }
    int br = -1;
    for (int i = 0; i <= width && i < len; i++) if (s[i] == ' ') br = i;
    if (br <= 0) { *consume = width; return width; }   /* no break point in range: hard cut */
    *consume = br + 1;                                  /* skip the break space */
    return br;
}

/* draw a bottom-anchored overlay panel: bg fill · rounded border · title (top-left) · hint (bottom-right) */
static void overlay_frame(int my, int mx, int mbot, int mw, const char *title, const char *hint) {
    for (int r = my; r <= mbot; r++) { ncplane_set_bg_rgb(g_std, COL_OV_BG);
        for (int x = mx; x < mx + mw; x++) ncplane_putchar_yx(g_std, r, x, ' '); }
    ncplane_set_fg_rgb(g_std, COL_OV_BORDER); ncplane_set_bg_rgb(g_std, COL_OV_BG);
    ncplane_putstr_yx(g_std, my, mx, "╭"); ncplane_putstr_yx(g_std, my, mx+mw-1, "╮");
    ncplane_putstr_yx(g_std, mbot, mx, "╰"); ncplane_putstr_yx(g_std, mbot, mx+mw-1, "╯");
    for (int x = mx+1; x < mx+mw-1; x++) { ncplane_putstr_yx(g_std, my, x, "─"); ncplane_putstr_yx(g_std, mbot, x, "─"); }
    for (int r = my+1; r < mbot; r++) { ncplane_putstr_yx(g_std, r, mx, "│"); ncplane_putstr_yx(g_std, r, mx+mw-1, "│"); }
    if (title) { ncplane_set_fg_rgb(g_std, COL_OV_TITLE); ncplane_set_bg_rgb(g_std, COL_OV_BG); ncplane_putstr_yx(g_std, my, mx+2, title); }
    if (hint) { ncplane_set_fg_rgb(g_std, COL_DIM); ncplane_set_bg_rgb(g_std, COL_OV_BG);
        ncplane_putstr_yx(g_std, mbot, mx+mw-1-(int)strlen(hint), hint); }
}
/* set a selectable row's background (selected = highlight fill); caller draws fg text after */
static void overlay_rowbg(int row, int mx, int mw, bool sel) {
    if (sel) { ncplane_set_bg_rgb(g_std, COL_OV_SELBG);
        for (int x = mx+1; x < mx+mw-1; x++) ncplane_putchar_yx(g_std, row, x, ' '); }
    else ncplane_set_bg_rgb(g_std, COL_OV_BG);
}
static void render(void) {
    unsigned R, C;
    if (g_resized) { notcurses_refresh(g_nc, NULL, NULL); g_resized = false; }  /* clear stale rows */
    notcurses_term_dim_yx(g_nc, &R, &C);
    if (R < 3 || C < 8) { notcurses_render(g_nc); return; }
    int W = (int)C, H = (int)R;
    ncplane_erase(g_std);
    g_click_kind = 0;                            /* rebuild the screen-row → overlay-item map each frame */
    for (int i = 0; i < H && i < 1024; i++) g_click_row[i] = -1;

    int box = (H >= 14) ? 1 : 0;                 /* bordered input box */
    int lm = box ? 2 : 0;                        /* left margin past the "│ " border */
    int contentW = box ? W - 1 : W;              /* text stops before the right border */
    /* input height — simulate the SAME wrap the input renderer uses (prompt + borders) */
    int in_rows; { int row = 0, col = 0;
        for (int i = 0; i < g_ilen; ) {
            int base = (row == 0) ? lm + 2 : lm;
            if (g_in[i] == '\n') { row++; col = 0; i++; continue; }
            unsigned char ch = (unsigned char)g_in[i];
            int cl = (ch>=0xF0)?4:(ch>=0xE0)?3:(ch>=0xC0)?2:1; if (i + cl > g_ilen) cl = 1;
            i += cl; col++;
            if (base + col >= contentW) { row++; col = 0; }
        }
        in_rows = row + 1;
    }
    if (in_rows > 6) in_rows = 6;

    /* zones (top->bottom): header | sep | transcript | status | menu | perm/spinner | [box]input | footer | pad.
       Input is computed first and pinned to the bottom so it can never be clipped. */
    int pad    = (H >= 12) ? 1 : 0;             /* blank padding row so the last line never clips */
    int footer = (H >= 9)  ? 1 : 0;             /* footer hint row */
    int topRsv = (H >= 13) ? 5 : (H >= 8) ? 2 : 0;   /* full header(5) → compact(info+sep=2) → none — degrade, don't vanish */
    int rFooter = footer ? H - 1 - pad : -1;
    int ibBot   = (footer ? rFooter : H - 1 - pad) - 1 - box;   /* last input CONTENT row */
    int maxin = ibBot - topRsv - 1; if (maxin < 1) maxin = 1;
    if (in_rows > maxin) in_rows = maxin;
    int iBot = ibBot;
    int iTop = iBot - in_rows + 1; if (iTop < topRsv + 1) iTop = topRsv + 1;
    int boxTop = iTop - box, boxBot = iBot + box;
    g_in_top = iTop; g_in_bot = iBot; g_in_lm = lm; g_in_cw = contentW;   /* for click-to-position */
    int spin = (g_busy && !g_perm && boxTop > topRsv) ? 1 : 0;  /* spinner row above the box */
    int spinTop = boxTop - spin;
    int permBot = spinTop - 1, perm_rows = 0, permTop = 0;
    if (g_perm && permBot >= topRsv + 1) {
        perm_rows = g_nopt + 3;                           /* question + Yes + suggestions + No */
        if (permBot - perm_rows + 1 < topRsv + 1) perm_rows = permBot - topRsv;
        if (perm_rows < 2) perm_rows = 2;
        permTop = permBot - perm_rows + 1;
    }
    int above = perm_rows ? permTop : spinTop;   /* the /command palette floats — no layout reservation */
    int hdr = topRsv;                                          /* body starts after header+separator */
    int sepRow = (topRsv >= 2) ? topRsv - 1 : -1;             /* header/body separator (full + compact) */
    int rStatus = above - 1;
    int body = ((rStatus >= 0) ? rStatus : above) - hdr;
    if (body < 0) body = 0;
    uint32_t bord = !strcmp(g_permmode,"acceptEdits") ? 0x4f8458      /* mode-colored borders (subdued) */
                  : !strcmp(g_permmode,"plan")        ? 0x5d77a8 : 0x59657e;
    uint32_t modecol = !strcmp(g_permmode,"acceptEdits") ? COL_OK   /* mode TEXT stays bright */
                     : !strcmp(g_permmode,"plan")        ? 0x82aaff : 0xb0bcd8;

    /* ---- transcript ---- */
    /* Wrap each block from its (ver,W,limit) cache — unchanged blocks cost nothing — then collect
       the visible lines as a pointer view. No full-transcript re-parse per frame. */
    g_nview = 0;
    for (size_t i = 0; i < g_nblk; i++) {
        Block *b = &g_blk[i];
        int limit = (b->kind == B_TOOL || b->kind == B_RESULT)
                  ? (g_expand ? 1000000 : (b->kind == B_RESULT ? 6 : 16)) : 0;
        block_layout(b, W, limit);
        for (int k = 0; k < b->ncrl; k++) view_push(&b->crl[k]);
        if (i + 1 < g_nblk) view_push(&g_sep);       /* blank line between blocks */
    }
    int total = g_nview, maxs = total > body ? total - body : 0;
    if (g_scroll > maxs) g_scroll = maxs;
    if (g_scroll < 0) g_scroll = 0;
    int first = total > body ? total - body - g_scroll : 0;
    if (first < 0) first = 0;
    g_v_hdr = hdr; g_v_body = body; g_v_first = first;   /* snapshot geometry for mouse hit-testing */
    int sSLi = 0, sSCol = 0, sELi = -1, sECol = 0;       /* normalized selection (start ≤ end) */
    if (g_sel) {
        bool af = g_sel_a_li < g_sel_c_li || (g_sel_a_li == g_sel_c_li && g_sel_a_col <= g_sel_c_col);
        sSLi = af ? g_sel_a_li : g_sel_c_li; sSCol = af ? g_sel_a_col : g_sel_c_col;
        sELi = af ? g_sel_c_li : g_sel_a_li; sECol = af ? g_sel_c_col : g_sel_a_col;
    }
    for (int r = 0; r < body; r++) {
        int li = first + r; if (li >= total) break;
        RLine *L = g_view[li];
        if (L->has_rowbg) {                          /* full-width diff row background */
            ncplane_set_bg_rgb(g_std, L->rowbg);
            for (int x = 0; x < W; x++) ncplane_putchar_yx(g_std, hdr + r, x, ' ');
            ncplane_set_bg_default(g_std);
        }
        int s0 = 0, s1 = 0;                          /* selected column range on this line */
        if (g_sel && li >= sSLi && li <= sELi) {
            int w = rline_width(L);
            s0 = (li == sSLi) ? sSCol : 0; s1 = (li == sELi) ? sECol : w;
            if (s0 < 0) s0 = 0;
            if (s1 > w) s1 = w;
            if (s1 < s0) s1 = s0;
        }
        draw_runs(hdr + r, L, s0, s1);
    }

    /* ---- persistent header: blank top line, sprite + identity + color-coded usage ---- */
    if (hdr >= 5) {
        int hy = 1;                          /* blank padding line at the very top */
        static const char *spr[3] = {" ▐▛███▜▌ ", "▝▜█████▛▘", "  ▘▘ ▝▝  "};   /* symmetric claude-code sprite */
        ncplane_set_bg_default(g_std); ncplane_set_fg_rgb(g_std, COL_BRAND);   /* same blue as footer keys */
        for (int r = 0; r < 3; r++) ncplane_putstr_yx(g_std, hy + r, 1, spr[r]);
        int tx = 12;
        ncplane_set_fg_rgb(g_std, 0xffffff); ncplane_set_styles(g_std, NCSTYLE_BOLD);
        char h0[120]; snprintf(h0, sizeof h0, "Claude Code %s", g_version[0]?g_version:"?");
        ncplane_putnstr_yx(g_std, hy+0, tx, (size_t)(W-tx), h0);
        ncplane_set_styles(g_std, NCSTYLE_NONE);
        char h1[200]; snprintf(h1, sizeof h1, "%s · %s%s%s", g_model[0]?g_model:"?", g_plan[0]?g_plan:"",
            g_effort[0] ? " · effort " : "", g_effort);
        ncplane_set_fg_rgb(g_std, 0xbcbcbc); ncplane_putnstr_yx(g_std, hy+1, tx, (size_t)(W-tx), h1);
        char h2[600]; snprintf(h2, sizeof h2, "%s", g_cwd[0]?g_cwd:"");
        ncplane_set_fg_rgb(g_std, 0x8c8c8c); ncplane_putnstr_yx(g_std, hy+2, tx, (size_t)(W-tx), h2);
        /* fixed-width usage panel: aligned label · bar · value across all rows */
        char ti[16]; fmt_k(ti, g_in_tok);
        int PANEL = 32, px = W - 1 - PANEL;
        if (px > tx + 1) {
            char rb[24], pc[16];
            if (g_u5 >= 0) { snprintf(pc, sizeof pc, "%d%%", (int)(g_u5+0.5)); fmt_reset(rb, g_u5r); usage_row(hy+0, px, PANEL, "5h",  g_u5/100.0, pc, rb); }
            if (g_u7 >= 0) { snprintf(pc, sizeof pc, "%d%%", (int)(g_u7+0.5)); fmt_reset(rb, g_u7r); usage_row(hy+1, px, PANEL, "wk",  g_u7/100.0, pc, rb); }
            long maxctx = strstr(g_model, "1m") ? 1000000 : 200000;
            char cmax[12]; if (maxctx >= 1000000) snprintf(cmax, sizeof cmax, "%.1fM", maxctx/1e6);
                           else snprintf(cmax, sizeof cmax, "%ldk", maxctx/1000);
            char cv[28]; snprintf(cv, sizeof cv, "%s/%s", ti, cmax);
            usage_row(hy+2, px, PANEL, "ctx", g_in_tok/(double)maxctx, cv, "");
        }
        if (sepRow >= 0) { ncplane_set_fg_rgb(g_std, COL_SEP);
            for (int x = 0; x < W; x++) ncplane_putstr_yx(g_std, sepRow, x, "─"); }
    }
    else if (hdr >= 2) {                          /* compact header: one info line + separator — stays put when short */
        ncplane_set_bg_default(g_std);
        ncplane_set_fg_rgb(g_std, COL_BRAND); ncplane_set_styles(g_std, NCSTYLE_BOLD);
        char hc[120]; snprintf(hc, sizeof hc, "Claude Code %s", g_version[0]?g_version:"?");
        ncplane_putnstr_yx(g_std, 0, 1, (size_t)(W-2), hc);
        ncplane_set_styles(g_std, NCSTYLE_NONE);
        int mx = 1 + dwidth(hc) + 1;
        char hm[160]; snprintf(hm, sizeof hm, "· %s%s%s", g_model[0]?g_model:"?", g_plan[0]?" · ":"", g_plan);
        ncplane_set_fg_rgb(g_std, 0xbcbcbc);
        if (mx < W - 2) ncplane_putnstr_yx(g_std, 0, mx, (size_t)(W-1-mx), hm);
        char us[96]; int un = 0; us[0] = 0;                /* usage summary, right-aligned */
        if (g_u5 >= 0) un += snprintf(us+un, sizeof us-un, "5h %d%%  ", (int)(g_u5+0.5));
        if (g_u7 >= 0) un += snprintf(us+un, sizeof us-un, "wk %d%%  ", (int)(g_u7+0.5));
        { char ti[16]; fmt_k(ti, g_in_tok); long mc = strstr(g_model,"1m")?1000000:200000;
          char cm[12]; if (mc>=1000000) snprintf(cm,sizeof cm,"%.1fM",mc/1e6); else snprintf(cm,sizeof cm,"%ldk",mc/1000);
          un += snprintf(us+un, sizeof us-un, "ctx %s/%s", ti, cm); }
        int ux = W - 1 - dwidth(us);
        if (ux > mx + dwidth(hm) + 2) { ncplane_set_fg_rgb(g_std, 0x8c9bb5); ncplane_putstr_yx(g_std, 0, ux, us); }
        if (sepRow >= 0) { ncplane_set_fg_rgb(g_std, COL_SEP);
            for (int x = 0; x < W; x++) ncplane_putstr_yx(g_std, sepRow, x, "─"); }
    }

    /* ---- body / input divider (stats now live in the header) ---- */
    if (rStatus >= 0) {
        ncplane_set_fg_rgb(g_std, COL_SEP); ncplane_set_bg_default(g_std);
        for (int x = 0; x < W; x++) ncplane_putstr_yx(g_std, rStatus, x, "─");
    }

    /* ---- permission box: numbered options (Yes / engine suggestions / No) ---- */
    if (perm_rows) {
        ncplane_set_bg_rgb(g_std, 0x23221a);
        for (int rr = permTop; rr <= permBot; rr++)
            for (int x = 0; x < W; x++) ncplane_putchar_yx(g_std, rr, x, ' ');
        ncplane_set_fg_rgb(g_std, 0xf2d765);
        char q[640];
        if (g_perm_isplan) snprintf(q, sizeof q, "▌ Ready to code? Review the plan above.");
        else snprintf(q, sizeof q, "▌ Allow %s?  %s", g_perm_tool?g_perm_tool:"tool", g_perm_desc?g_perm_desc:"");
        ncplane_putnstr_yx(g_std, permTop, 0, (size_t)W, q);
        int plast = g_nopt + 1;
        g_click_kind = 'p';
        for (int o = 0; o <= plast; o++) {
            int row = permTop + 1 + o; if (row > permBot) break;
            if (row >= 0 && row < 1024) g_click_row[row] = o;
            const char *label = (o == 0)     ? (g_perm_isplan ? "Yes, proceed" : "Yes")
                              : (o == plast) ? (g_perm_isplan ? "No, keep planning" : "No")
                              : g_opt_label[o-1];
            char line[220]; snprintf(line, sizeof line, "   %d. %s", o + 1, label);
            if (o == g_psel) { ncplane_set_fg_rgb(g_std, 0x17130a); ncplane_set_bg_rgb(g_std, 0xa3883e);
                for (int x = 0; x < W; x++) ncplane_putchar_yx(g_std, row, x, ' '); }
            else { ncplane_set_fg_rgb(g_std, 0xe7dcb0); ncplane_set_bg_rgb(g_std, 0x23221a); }
            ncplane_putnstr_yx(g_std, row, 0, (size_t)W, line);
        }
        ncplane_set_bg_default(g_std);
    }

    /* ---- input box (bordered, mode-colored; content drawn per grapheme so it always shows) ---- */
    {
        if (box) {
            ncplane_set_fg_rgb(g_std, bord); ncplane_set_bg_default(g_std);
            ncplane_putstr_yx(g_std, boxTop, 0, "╭");
            ncplane_putstr_yx(g_std, boxBot, 0, "╰");
            for (int x = 1; x < W-1; x++) { ncplane_putstr_yx(g_std, boxTop, x, "─"); ncplane_putstr_yx(g_std, boxBot, x, "─"); }
            ncplane_putstr_yx(g_std, boxTop, W-1, "╮");
            ncplane_putstr_yx(g_std, boxBot, W-1, "╯");
            for (int rr = iTop; rr <= iBot; rr++) { ncplane_putstr_yx(g_std, rr, 0, "│"); ncplane_putstr_yx(g_std, rr, W-1, "│"); }
        }
        ncplane_set_bg_default(g_std);
        if (g_rsearch) {                                     /* reverse history search prompt */
            const char *p1 = "(reverse-i-search)`";
            ncplane_set_fg_rgb(g_std, 0x9a9aa2);
            ncplane_putnstr_yx(g_std, iTop, lm, (size_t)(contentW - lm), p1);
            int qx = lm + dwidth(p1);
            ncplane_set_fg_rgb(g_std, 0xffffff);
            if (qx < contentW) ncplane_putnstr_yx(g_std, iTop, qx, (size_t)(contentW - qx), g_rquery);
            int after = qx + dwidth(g_rquery);
            ncplane_set_fg_rgb(g_std, 0x9a9aa2);
            if (after < contentW) ncplane_putnstr_yx(g_std, iTop, after, (size_t)(contentW - after), "': ");
            int mx = after + 3;
            const char *m = (g_rmatch >= 0) ? g_hist[g_rmatch] : "(no match)";
            const char *hit = (g_rmatch >= 0 && g_rqlen > 0) ? strstr(m, g_rquery) : NULL;  /* same matcher as rsearch_find */
            if (mx >= contentW) { /* no room */ }
            else if (hit) {                                  /* draw prefix · matched substring (amber) · suffix */
                char seg[512]; int pre = (int)(hit - m);
                int n1 = pre < (int)sizeof seg - 1 ? pre : (int)sizeof seg - 1;
                memcpy(seg, m, (size_t)n1); seg[n1] = 0;
                ncplane_set_fg_rgb(g_std, 0xe6e6e6); ncplane_set_bg_default(g_std);
                ncplane_putnstr_yx(g_std, iTop, mx, (size_t)(contentW - mx), seg);
                int c2 = mx + dwidth(seg);
                int n2 = g_rqlen < (int)sizeof seg - 1 ? g_rqlen : (int)sizeof seg - 1;
                memcpy(seg, m + pre, (size_t)n2); seg[n2] = 0;
                ncplane_set_fg_rgb(g_std, 0x17130a); ncplane_set_bg_rgb(g_std, COL_WARN);
                if (c2 < contentW) ncplane_putnstr_yx(g_std, iTop, c2, (size_t)(contentW - c2), seg);
                int c3 = c2 + dwidth(seg); ncplane_set_bg_default(g_std);
                ncplane_set_fg_rgb(g_std, 0xe6e6e6);
                if (c3 < contentW) ncplane_putnstr_yx(g_std, iTop, c3, (size_t)(contentW - c3), m + pre + g_rqlen);
            } else {
                ncplane_set_fg_rgb(g_std, g_rmatch >= 0 ? 0xe6e6e6 : 0xf38ba8);
                ncplane_putnstr_yx(g_std, iTop, mx, (size_t)(contentW - mx), m);
            }
            int cx = after < contentW ? after : contentW - 1;
            g_cur_on = true; g_cur_y = iTop; g_cur_x = cx; g_cur_gc[0] = ' '; g_cur_gc[1] = 0;
        } else {
        bool vnorm = g_vim && !g_vins;                /* vim normal mode: amber block prompt */
        ncplane_set_fg_rgb(g_std, vnorm ? COL_WARN : COL_BRAND);
        ncplane_putstr_yx(g_std, iTop, lm, vnorm ? "▌ " : "> ");
        ncplane_set_fg_rgb(g_std, 0xffffff);
        int cy = iTop, cx = lm + 2, row = iTop, col = 0; bool placed = false;
        int va = 0, vb = 0; if (g_vvisual) visual_range(&va, &vb);   /* highlight the visual selection */
        for (int i = 0; i <= g_ilen; ) {
            int base = (row == iTop) ? lm + 2 : lm;
            if (i == g_icur) { cy = row; cx = base + col; placed = true;
                if (i < g_ilen && g_in[i] != '\n') {                  /* capture the glyph under the cursor (drawn in reverse) */
                    unsigned char pc = (unsigned char)g_in[i];
                    int pl = (pc>=0xF0)?4:(pc>=0xE0)?3:(pc>=0xC0)?2:1; if (i+pl>g_ilen) pl = 1;
                    memcpy(g_cur_gc, g_in+i, (size_t)pl); g_cur_gc[pl] = 0;
                } else { g_cur_gc[0] = ' '; g_cur_gc[1] = 0; }
            }
            if (i >= g_ilen) break;
            unsigned char ch = (unsigned char)g_in[i];
            if (ch == '\n') { row++; col = 0; i++; if (row > iBot) break; continue; }
            int cl = (ch >= 0xF0) ? 4 : (ch >= 0xE0) ? 3 : (ch >= 0xC0) ? 2 : 1;   /* utf8 length */
            if (i + cl > g_ilen) cl = 1;
            int xx = base + col;
            if (xx < contentW) {
                char gc[8]; memcpy(gc, g_in + i, (size_t)cl); gc[cl] = 0;
                if (g_vvisual && i >= va && i < vb) ncplane_set_bg_rgb(g_std, SEL_BG);
                else ncplane_set_bg_default(g_std);
                ncplane_putnstr_yx(g_std, row, xx, (size_t)cl, gc);
            }
            i += cl; col++;
            if (base + col >= contentW) { row++; col = 0; }
            if (row > iBot) break;
        }
        ncplane_set_bg_default(g_std);
        if (!placed) { cy = iTop; cx = lm + 2; g_cur_gc[0] = ' '; g_cur_gc[1] = 0; }
        if (cy > iBot) cy = iBot;
        if (g_perm) g_cur_on = false;                        /* answering a prompt, not typing */
        else { g_cur_on = true; g_cur_y = cy; g_cur_x = cx; }
        }
    }

    /* ---- working spinner (animated, above the input) ---- */
    if (spin) {
        static const char *FR[] = {"✻","✶","✷","✸","✹","✺"};
        const char *g = FR[(now_ms() / 280) % 6];     /* time-based: animates independent of render rate */
        long el = (long)time(NULL) - g_turn_start;
        char tm[24]; if (el >= 60) snprintf(tm, sizeof tm, "%ldm %02lds", el/60, el%60); else snprintf(tm, sizeof tm, "%lds", el);
        double toks = g_turn_bytes / 3.6; if (g_think_est > toks) toks = g_think_est;   /* realtime estimate */
        char head[48]; snprintf(head, sizeof head, "%s %s…  ", g, spin_word());
        ncplane_set_bg_default(g_std);
        ncplane_set_fg_rgb(g_std, 0xe08aa6); ncplane_putstr_yx(g_std, spinTop, 0, head);
        char tail[64];
        if (toks > 0) { char tk[16]; fmt_k(tk, toks); snprintf(tail, sizeof tail, "(%s · ↓ %s tokens)", tm, tk); }
        else snprintf(tail, sizeof tail, "(%s)", tm);
        ncplane_set_fg_rgb(g_std, 0x9a9aa2); ncplane_putstr_yx(g_std, spinTop, dwidth(head), tail);
    }

    /* ---- footer hint (parity with the real CLI's bottom row) ---- */
    if (rFooter >= 0) {
        ncplane_set_bg_default(g_std);
        int fx = 1;
        struct fseg { const char *t; uint32_t c; };
        struct fseg normseg[] = {                        /* idle/typing: input keys */
            { "▸▸ ", modecol }, { mode_label(g_permmode), modecol }, { "  (shift+tab to cycle)", COL_HINT },
            { "    ", 0x4a4a4a },
            { "enter", COL_OK }, { " send", COL_HINT }, { "   ", 0x4a4a4a },
            { "esc", 0xe0a35a }, { " stop", COL_HINT }, { "   ", 0x4a4a4a },
            { "^c", 0xf38ba8 }, { " quit", COL_HINT },
        };
        struct fseg permseg[] = {                         /* permission prompt: only enter answers */
            { "▸▸ ", COL_WARN }, { "permission required", COL_WARN }, { "    ", 0x4a4a4a },
            { "↑↓", COL_BRAND }, { " move", COL_HINT }, { "   ", 0x4a4a4a },
            { "enter", COL_OK }, { " select", COL_HINT }, { "   ", 0x4a4a4a },
            { "esc", 0xe0a35a }, { " deny", COL_HINT },
        };
        struct fseg *seg = g_perm ? permseg : normseg;
        size_t nseg = g_perm ? sizeof permseg/sizeof permseg[0] : sizeof normseg/sizeof normseg[0];
        for (size_t s = 0; s < nseg; s++) {
            int len = dwidth(seg[s].t);
            if (fx + len <= W) { ncplane_set_fg_rgb(g_std, seg[s].c); ncplane_putstr_yx(g_std, rFooter, fx, seg[s].t); }
            fx += len;
        }
        /* session id at a FIXED position (state has its own reserved field so nothing jumps) */
        const int STATEW = 14;
        uint32_t scol = g_busy ? COL_WARN : (!strcmp(g_status,"idle") ? COL_OK : 0x5fd7d7);
        int stx = W - dwidth(g_status) - 1;
        char ses[48]; snprintf(ses, sizeof ses, "session %s", g_session);
        int sesx = W - 1 - STATEW - 2 - (int)strlen(ses);
        if (sesx > fx + 2) { ncplane_set_fg_rgb(g_std, 0x6b6b73); ncplane_putstr_yx(g_std, rFooter, sesx, ses); }
        if (g_cost > 0) {                            /* running session cost, dim, left of the session id */
            char cst[24]; if (g_cost < 1) snprintf(cst, sizeof cst, "$%.4f", g_cost);
                          else            snprintf(cst, sizeof cst, "$%.2f", g_cost);
            int cx = sesx - (int)strlen(cst) - 2;
            if (cx > fx + 2) { ncplane_set_fg_rgb(g_std, 0x5f8f6f); ncplane_putstr_yx(g_std, rFooter, cx, cst); }
        }
        if (stx > fx + 1) { ncplane_set_fg_rgb(g_std, scol); ncplane_putstr_yx(g_std, rFooter, stx, g_status); }
        if (g_toast[0] && now_ms() < g_toast_until) {    /* transient notice (e.g. copy) over the left hints */
            ncplane_set_bg_default(g_std); ncplane_set_fg_rgb(g_std, COL_OK);
            ncplane_putnstr_yx(g_std, rFooter, 1, (size_t)(W - 2), g_toast);
        }
        if (g_vvisual) {                                 /* vim visual-mode indicator over the left hints */
            ncplane_set_bg_default(g_std); ncplane_set_fg_rgb(g_std, 0xc792ea);
            ncplane_putstr_yx(g_std, rFooter, 1, g_vvisual == 'V' ? "-- VISUAL LINE --" : "-- VISUAL --");
        }
    }
    /* ---- floating /command · @file palette (tall, full-width, wrapped descriptions) ---- */
    if (g_menu && g_nmatch > 0) {
        int px = 0, pw = W;                          /* full width: edges align with the input box below */
        int namex = px + 2;
        int dc = px + 26;                            /* description column (name field ~23 wide) */
        int descW = (px + pw - 2) - dc; if (descW < 12) descW = 12;
        const int MAXDL = 3;                         /* cap each description at 3 wrapped lines */
        uint32_t pbg = COL_OV_BG;

        /* pass 1: per-entry height = max(1, wrapped description lines, capped) */
        int h[768];
        for (int i = 0; i < g_nmatch; i++) {
            const char *d = g_mdesc[i]; int dl = (int)strlen(d), off = 0, lines = 0;
            while (off < dl && lines < MAXDL) { int c; pal_wrap(d + off, dl - off, descW, &c); off += c; lines++; }
            h[i] = lines < 1 ? 1 : lines;
        }
        /* vertical extent: grow with content, capped to the space above the input box */
        int pbot = boxTop - 1, topLimit = hdr;
        int maxInner = pbot - topLimit - 1; if (maxInner < 1) maxInner = 1;
        int total = 0; for (int i = 0; i < g_nmatch; i++) total += h[i];
        int inner = total < maxInner ? total : maxInner;
        int ptop = pbot - inner - 1; if (ptop < topLimit) ptop = topLimit;
        /* window: pick first visible entry mb so the selected entry is fully shown */
        int mb = 0;
        for (;;) {
            int used = 0, last = mb - 1;
            for (int i = mb; i < g_nmatch; i++) { if (used + h[i] > inner) break; used += h[i]; last = i; }
            if (g_msel <= last || mb >= g_nmatch - 1) break;
            mb++;
        }

        char title[64]; snprintf(title, sizeof title, " %s · %d ", g_menu_kind=='@'?"files":"commands", g_nmatch);
        overlay_frame(ptop, px, pbot, pw, title, NULL);

        int row = ptop + 1;
        for (int idx = mb; idx < g_nmatch && row <= pbot - 1; idx++) {
            bool sel = (idx == g_msel);
            int eh = h[idx]; if (row + eh - 1 > pbot - 1) eh = pbot - 1 - row + 1;   /* clip last entry */
            if (eh < 1) break;
            for (int rr = 0; rr < eh; rr++) {        /* highlight the whole entry when selected */
                ncplane_set_bg_rgb(g_std, sel ? COL_OV_SELBG : pbg);
                for (int x = px+1; x < px+pw-1; x++) ncplane_putchar_yx(g_std, row+rr, x, ' ');
                if (row+rr >= 0 && row+rr < 1024) { g_click_row[row+rr] = idx; g_click_kind = 'm'; }
            }
            ncplane_set_bg_rgb(g_std, sel ? COL_OV_SELBG : pbg);
            ncplane_set_fg_rgb(g_std, sel ? 0xffffff : COL_OV_ITEM);
            ncplane_putnstr_yx(g_std, row, namex, (size_t)(dc - namex - 1), g_match[idx]);
            const char *d = g_mdesc[idx]; int dl = (int)strlen(d), off = 0;
            ncplane_set_fg_rgb(g_std, sel ? 0xdce6f7 : COL_DIM);
            for (int ln = 0; ln < eh && off < dl; ln++) {
                int c; int seg = pal_wrap(d + off, dl - off, descW, &c);
                bool truncd = (ln == eh - 1) && (off + c < dl);   /* last allowed line but more remains */
                char tmp[512]; int sw = seg; if (truncd && sw > descW - 1) sw = descW - 1;
                if (sw > (int)sizeof tmp - 1) sw = (int)sizeof tmp - 1;
                memcpy(tmp, d + off, (size_t)sw); tmp[sw] = 0;
                ncplane_putnstr_yx(g_std, row+ln, dc, (size_t)descW, tmp);
                if (truncd) ncplane_putstr_yx(g_std, row+ln, dc + sw, "…");
                off += c;
            }
            row += eh;
        }
        if (total > inner) {                         /* scroll position indicator */
            char si[32]; snprintf(si, sizeof si, " %d/%d ", g_msel+1, g_nmatch);
            ncplane_set_fg_rgb(g_std, COL_DIM); ncplane_set_bg_rgb(g_std, pbg);
            ncplane_putstr_yx(g_std, pbot, px+pw-1-(int)strlen(si), si);
        }
        ncplane_set_bg_default(g_std);
    }

    /* ---- quit-confirmation modal (command-palette style, centered) ---- */
    if (g_confirm_quit) {
        const char *opts[2] = { "Yes, quit", "No, keep working" };
        int mw = 38; if (mw > W - 4) mw = W - 4;
        int mh = 4;                                  /* inner: message, blank, 2 options */
        int mx = (W - mw) / 2; if (mx < 0) mx = 0;
        int mbot = boxTop - 1;                        /* hug the bottom, just above the input box */
        int my = mbot - mh - 1;
        if (my < hdr + 1) { my = hdr + 1; mbot = my + mh + 1; }
        overlay_frame(my, mx, mbot, mw, " quit? ", " enter · esc cancel ");
        ncplane_set_fg_rgb(g_std, 0xd6d6d6); ncplane_set_bg_rgb(g_std, COL_OV_BG);
        ncplane_putnstr_yx(g_std, my+1, mx+3, (size_t)(mw-5), "End this session?");
        for (int o = 0; o < 2; o++) {
            int row = my + 3 + o; bool sel = (o == g_qsel);
            overlay_rowbg(row, mx, mw, sel);
            ncplane_set_fg_rgb(g_std, sel ? 0xffffff : COL_OV_ITEM);
            char line[64]; snprintf(line, sizeof line, "  %d. %s", o+1, opts[o]);
            ncplane_putnstr_yx(g_std, row, mx+2, (size_t)(mw-4), line);
        }
        ncplane_set_bg_default(g_std);
        g_cur_on = false;
    }

    /* ---- resume picker (full width, bottom-anchored, grows to fit — like the /command palette) ---- */
    if (g_resume_open && g_nsess > 0) {
        int mx = 0, mw = W;
        int mbot = boxTop - 1, topLimit = hdr;   /* hug the bottom, just above the input box */
        int maxRows = mbot - topLimit - 1; if (maxRows < 1) maxRows = 1;
        int rows = g_nsess < maxRows ? g_nsess : maxRows;
        int my = mbot - rows - 1; if (my < topLimit) my = topLimit;
        int sb = 0;                                  /* scroll window so the selection stays visible */
        if (g_ssel >= rows) sb = g_ssel - rows + 1;
        if (sb > g_nsess - rows) sb = g_nsess - rows;
        if (sb < 0) sb = 0;
        char title[48]; snprintf(title, sizeof title, " resume · %d ", g_nsess);
        overlay_frame(my, mx, mbot, mw, title, " enter resume · f fork · esc cancel ");
        long now = (long)time(NULL);
        for (int m = 0; m < rows; m++) {
            int idx = sb + m; if (idx >= g_nsess) break;
            int row = my + 1 + m; bool sel = (idx == g_ssel);
            if (row >= 0 && row < 1024) { g_click_row[row] = idx; g_click_kind = 'r'; }
            Sess *s = &g_sess[idx];
            overlay_rowbg(row, mx, mw, sel);
            char rel[32]; long ag = now - s->mtime; if (ag < 0) ag = 0;
            if (ag < 3600) snprintf(rel, sizeof rel, "%ldm ago", ag/60);
            else if (ag < 86400) snprintf(rel, sizeof rel, "%ldh ago", ag/3600);
            else snprintf(rel, sizeof rel, "%ldd ago", ag/86400);
            int relw = (int)strlen(rel);
            ncplane_set_fg_rgb(g_std, sel ? 0xbcd0ff : COL_OV_BORDER);
            ncplane_putnstr_yx(g_std, row, mx+2, 8, s->id);
            int lx = mx + 12, lw = mw - 12 - relw - 3;
            const char *disp = s->name[0] ? s->name : s->label;     /* named sessions show the name, in brand blue */
            ncplane_set_fg_rgb(g_std, s->name[0] ? (sel ? 0xbcd0ff : COL_BRAND) : (sel ? 0xffffff : COL_OV_ITEM));
            if (lw > 0) ncplane_putnstr_yx(g_std, row, lx, (size_t)lw, disp);
            ncplane_set_fg_rgb(g_std, sel ? 0xbcd0ff : COL_DIM);
            ncplane_putstr_yx(g_std, row, mx+mw-1-relw-1, rel);
        }
        ncplane_set_bg_default(g_std);
        g_cur_on = false;
    }

    /* ---- choice picker (model / effort / rewind) — full width, bottom-anchored, grows to fit ---- */
    if (g_choice_open && g_nchoice > 0) {
        int mx = 0, mw = W;
        int mbot = boxTop - 1, topLimit = hdr;
        int maxRows = mbot - topLimit - 1; if (maxRows < 1) maxRows = 1;
        int rows = g_nchoice < maxRows ? g_nchoice : maxRows;
        int my = mbot - rows - 1; if (my < topLimit) my = topLimit;
        int sb = 0;
        if (g_chsel >= rows) sb = g_chsel - rows + 1;
        if (sb > g_nchoice - rows) sb = g_nchoice - rows;
        if (sb < 0) sb = 0;
        char title[48]; snprintf(title, sizeof title, " %s · %d ", g_choice_title, g_nchoice);
        overlay_frame(my, mx, mbot, mw, title, " enter select · esc cancel ");
        for (int m = 0; m < rows; m++) {
            int idx = sb + m; if (idx >= g_nchoice) break;
            int row = my + 1 + m; bool sel = (idx == g_chsel);
            if (row >= 0 && row < 1024) { g_click_row[row] = idx; g_click_kind = 'c'; }
            overlay_rowbg(row, mx, mw, sel);
            ncplane_set_fg_rgb(g_std, sel ? 0xffffff : COL_OV_ITEM);
            char line[160]; snprintf(line, sizeof line, "  %d. %s", idx + 1, g_choice[idx]);
            ncplane_putnstr_yx(g_std, row, mx+2, (size_t)(mw-4), line);
        }
        ncplane_set_bg_default(g_std);
        g_cur_on = false;
    }

    ncplane_set_fg_default(g_std);
    if (g_cur_on) {                                  /* self-drawn steady block cursor — no hardware cursor, no per-frame flicker */
        ncplane_set_styles(g_std, NCSTYLE_NONE);
        ncplane_set_fg_rgb(g_std, 0x10131a); ncplane_set_bg_rgb(g_std, 0xc7d0e0);
        ncplane_putnstr_yx(g_std, g_cur_y, g_cur_x, strlen(g_cur_gc), g_cur_gc);
        ncplane_set_bg_default(g_std); ncplane_set_fg_default(g_std);
    }
    notcurses_render(g_nc);
}

/* ---- vim normal-mode editing (toggled by /vim; esc enters normal, i/a/o… return to insert) ---- */
static void vim_del_line(void) {
    int s = line_start(g_icur), e = line_end(g_icur);
    int kn = e - s;                                    /* yank the line (normalized trailing newline) so dd→p works */
    if (kn >= 0 && kn + 1 < (int)sizeof g_kill) { memcpy(g_kill, g_in + s, (size_t)kn); g_kill[kn] = '\n'; g_killn = kn + 1; g_kill_linewise = true; }
    if (e < g_ilen && g_in[e] == '\n') e++;            /* take the trailing newline */
    else if (s > 0 && g_in[s-1] == '\n') s--;          /* last line: take the leading newline */
    undo_mark();
    memmove(g_in + s, g_in + e, (size_t)(g_ilen - e));
    g_ilen -= (e - s); g_in[g_ilen] = 0; g_icur = s;
    if (g_icur > g_ilen) g_icur = g_ilen;
    g_undo_at = g_icur;
}
/* byte range [a,b) covered by the current visual selection (charwise inclusive of the cursor; V = whole lines) */
static void visual_range(int *a, int *b) {
    int lo = g_vanchor < g_icur ? g_vanchor : g_icur;
    int hi = g_vanchor < g_icur ? g_icur : g_vanchor;
    if (g_vvisual == 'V') { lo = line_start(lo); hi = line_end(hi); if (hi < g_ilen && g_in[hi] == '\n') hi++; }
    else hi = utf8_next(g_in, hi, g_ilen);   /* include the char under the cursor */
    if (lo < 0) lo = 0;
    if (hi > g_ilen) hi = g_ilen;
    *a = lo; *b = hi;
}
/* paste the kill buffer: linewise → a new line below (p) / above (P); charwise → after (p) / at (P) the cursor */
static void vim_paste(bool before) {
    if (g_killn <= 0) return;
    if (g_kill_linewise) {
        bool nl = (g_kill[g_killn-1] == '\n');
        int content = nl ? g_killn - 1 : g_killn;
        if (before) { g_icur = line_start(g_icur); int at = g_icur; in_insert(g_kill, content); in_insert("\n", 1); g_icur = at; }
        else        { g_icur = line_end(g_icur);   in_insert("\n", 1); int at = g_icur; in_insert(g_kill, content); g_icur = at; }
    } else {
        if (!before && g_icur < g_ilen) g_icur = utf8_next(g_in, g_icur, g_ilen);
        in_insert(g_kill, g_killn);
    }
}
static int g_vcount = 0;                                        /* pending vim count, e.g. 3 in 3dd / 5j */
static void vim_normal(uint32_t id, const ncinput *ni) {
    char op = g_vop; g_vop = 0;
    int cnt = g_vcount ? g_vcount : 1;
    if (id == NCKEY_ENTER) { g_vcount = 0; submit_input(); return; }          /* submit from normal mode */
    if (id == NCKEY_ESC)   { g_vcount = 0; g_vvisual = 0; return; }           /* exit visual / clear count */
    if (id == NCKEY_LEFT)  { g_vcount = 0; while (cnt--) g_icur = utf8_prev(g_in, g_icur); return; }
    if (id == NCKEY_RIGHT) { g_vcount = 0; while (cnt--) g_icur = utf8_next(g_in, g_icur, g_ilen); return; }
    if (id == NCKEY_UP)    { g_vcount = 0; while (cnt--) cursor_up(); return; }
    if (id == NCKEY_DOWN)  { g_vcount = 0; while (cnt--) cursor_down(); return; }
    if (id == NCKEY_BACKSPACE) { g_vcount = 0; while (cnt--) g_icur = utf8_prev(g_in, g_icur); return; }
    if (nckey_synthesized_p(id) || id < 0x20 || !ni->utf8[0]) { g_vcount = 0; return; }
    char c = (char)id;
    if ((c >= '1' && c <= '9') || (c == '0' && g_vcount > 0)) {  /* build the count ('0' alone is a motion) */
        g_vcount = g_vcount * 10 + (c - '0'); if (g_vcount > 99999) g_vcount = 99999;
        g_vop = op;                                             /* keep any pending operator across the digits */
        return;
    }
    if (g_vvisual && (c=='d'||c=='x'||c=='c'||c=='s'||c=='y')) {  /* operate on the visual selection, then exit */
        bool lw = (g_vvisual == 'V');
        int va, vb; visual_range(&va, &vb);
        if (c == 'y') { int kn = vb - va; if (kn > 0 && kn < (int)sizeof g_kill) { memcpy(g_kill, g_in+va, (size_t)kn); g_killn = kn; } g_icur = va; }
        else { g_icur = va; kill_range(va, vb); if (c == 'c' || c == 's') g_vins = true; }
        g_kill_linewise = lw;
        g_vvisual = 0; g_vcount = 0; menu_update(); return;
    }
    int ls = line_start(g_icur), le = line_end(g_icur);
    if (op == 'g') { g_vcount = 0; if (c == 'g') g_icur = 0; menu_update(); return; }   /* gg */
    if (op == 'd' || op == 'c') {                               /* operator + motion: dd cc dw cw d$ … (count repeats) */
        int n = g_vcount ? g_vcount : 1; g_vcount = 0; bool chg = (op == 'c');
        if ((op == 'd' && c == 'd') || (op == 'c' && c == 'c')) {
            if (op == 'd') { for (int k = 0; k < n; k++) vim_del_line(); }
            else { kill_range(line_start(g_icur), line_end(g_icur)); g_vins = true; }   /* cc: change the line's text */
        }
        else if (c == 'w' || c == 'e') { for (int k = 0; k < n; k++) kill_range(g_icur, word_right(g_icur)); if (chg) g_vins = true; }
        else if (c == 'b') { for (int k = 0; k < n; k++) kill_range(word_left(g_icur), g_icur); if (chg) g_vins = true; }
        else if (c == '$') { kill_to_eol(); if (chg) g_vins = true; }
        else if (c == '0') { kill_to_bol(); if (chg) g_vins = true; }
        menu_update(); return;
    }
    if (op == 'y') {                                            /* yank (no delete): yy yw ye yb y$ y0 */
        int n = g_vcount ? g_vcount : 1; g_vcount = 0;
        int a = g_icur, b = g_icur; bool lw = false;
        if (c == 'y') { a = line_start(g_icur); b = g_icur; for (int k = 0; k < n; k++) { b = line_end(b); if (b < g_ilen && g_in[b] == '\n') b++; } lw = true; }
        else if (c == 'w' || c == 'e') { for (int k = 0; k < n; k++) b = word_right(b); }
        else if (c == 'b') { for (int k = 0; k < n; k++) a = word_left(a); }
        else if (c == '$') { b = line_end(g_icur); }
        else if (c == '0') { a = line_start(g_icur); }
        else { menu_update(); return; }
        int kn = b - a; if (kn > 0 && kn < (int)sizeof g_kill) { memcpy(g_kill, g_in + a, (size_t)kn); g_killn = kn; g_kill_linewise = lw; }
        g_icur = a; menu_update(); return;
    }
    if (c == 'd') { g_vop = 'd'; return; }                       /* set operator, preserving any count for the motion */
    if (c == 'c') { g_vop = 'c'; return; }
    if (c == 'y') { g_vop = 'y'; return; }
    if (c == 'g') { g_vop = 'g'; return; }
    int n = g_vcount ? g_vcount : 1; g_vcount = 0;
    switch (c) {
        case 'h': while (n--) g_icur = utf8_prev(g_in, g_icur); break;
        case 'l': while (n--) g_icur = utf8_next(g_in, g_icur, g_ilen); break;
        case 'j': while (n--) cursor_down(); break;
        case 'k': while (n--) cursor_up(); break;
        case '0': case '^': g_icur = ls; break;
        case '$': g_icur = le; break;
        case 'w': case 'e': while (n--) g_icur = word_right(g_icur); break;
        case 'b': while (n--) g_icur = word_left(g_icur); break;
        case 'G': g_icur = g_ilen; break;
        case 'v': g_vvisual = (g_vvisual == 'v') ? 0 : 'v'; g_vanchor = g_icur; break;   /* charwise visual */
        case 'V': g_vvisual = (g_vvisual == 'V') ? 0 : 'V'; g_vanchor = g_icur; break;   /* linewise visual */
        case 'u': while (n--) undo_apply(); break;               /* undo */
        case 'p': while (n--) vim_paste(false); break;           /* paste after / below */
        case 'P': while (n--) vim_paste(true);  break;           /* paste before / above */
        case 'Y': { int a = line_start(g_icur), b = g_icur;      /* yank n lines (= yy) */
            for (int k = 0; k < n; k++) { b = line_end(b); if (b < g_ilen && g_in[b] == '\n') b++; }
            int kn = b - a; if (kn > 0 && kn < (int)sizeof g_kill) { memcpy(g_kill, g_in + a, (size_t)kn); g_killn = kn; g_kill_linewise = true; } } break;
        case 'i': g_vins = true; break;
        case 'a': g_icur = utf8_next(g_in, g_icur, g_ilen); g_vins = true; break;
        case 'I': g_icur = ls; g_vins = true; break;
        case 'A': g_icur = le; g_vins = true; break;
        case 'o': g_icur = le; in_insert("\n", 1); g_vins = true; break;
        case 'O': g_icur = ls; in_insert("\n", 1); g_icur = ls; g_vins = true; break;
        case 'x': while (n--) in_delete(); break;
        case 'D': kill_to_eol(); break;
        case 'C': kill_to_eol(); g_vins = true; break;
        default: break;
    }
    if (g_vins) g_vvisual = 0;                                   /* entering insert leaves visual mode */
    menu_update();
}
/* ====================================================== keys ============= */
/* map a screen cell (y,x) to a view-line index + column; clamps y into the body so a drag past
   the top/bottom edge keeps extending the selection. inbody = was the cell actually in the transcript. */
static void sel_hit(int y, int x, int *li, int *col, bool *inbody) {
    int r = y - g_v_hdr;
    *inbody = (r >= 0 && r < g_v_body && g_nview > 0);
    if (r < 0) r = 0;
    else if (r >= g_v_body) r = g_v_body - 1;
    if (r < 0) r = 0;                                  /* g_v_body == 0 */
    int idx = g_v_first + r;
    if (idx < 0) idx = 0;
    else if (idx > g_nview - 1) idx = g_nview > 0 ? g_nview - 1 : 0;
    *li = idx; *col = x < 0 ? 0 : x;
}
/* button1 press/drag/release → drive the selection (drag-motion arrives as further BUTTON1 events). */
static void sel_mouse(const ncinput *ni) {
    int li, col; bool inbody; sel_hit(ni->y, ni->x, &li, &col, &inbody);
    g_drag_y = ni->y;                                /* track for edge autoscroll */
    if (ni->evtype == NCTYPE_RELEASE) {
        g_seldrag = false;
        if (g_sel && g_sel_a_li == g_sel_c_li && g_sel_a_col == g_sel_c_col) g_sel = false;  /* plain click, no drag */
        return;
    }
    if (!g_seldrag) {                                /* initial press */
        if (!inbody) { g_sel = false; return; }      /* click outside the transcript clears any selection */
        g_seldrag = true; g_sel = true;
        g_sel_a_li = g_sel_c_li = li; g_sel_a_col = g_sel_c_col = col;
    } else {                                          /* drag motion: extend to the cursor */
        g_sel_c_li = li; g_sel_c_col = col;
    }
}
static void clipboard_copy(const char *s, int n) {
    FILE *pp = popen("{ wl-copy 2>/dev/null || xclip -selection clipboard -i 2>/dev/null ; }", "w");
    if (!pp) return;
    fwrite(s, 1, (size_t)n, pp);
    pclose(pp);
}
/* copy the selected view lines (joined by newlines) to the system clipboard, then clear the selection. */
static void sel_copy(void) {
    if (!g_sel) return;
    bool af = g_sel_a_li < g_sel_c_li || (g_sel_a_li == g_sel_c_li && g_sel_a_col <= g_sel_c_col);
    int sLi = af ? g_sel_a_li : g_sel_c_li, sCol = af ? g_sel_a_col : g_sel_c_col;
    int eLi = af ? g_sel_c_li : g_sel_a_li, eCol = af ? g_sel_c_col : g_sel_a_col;
    char *buf = NULL; size_t cap = 0, len = 0;
    for (int li = sLi; li <= eLi && li < g_nview; li++) {
        RLine *L = g_view[li];
        int w = rline_width(L);                          /* character columns */
        int c0 = (li == sLi) ? sCol : 0, c1 = (li == eLi) ? eCol : w;
        if (c0 < 0) c0 = 0;
        if (c1 > w) c1 = w;
        if (c1 < c0) c1 = c0;
        int cc = 0;
        for (int i = 0; i < L->n; i++) {
            Run *r = &L->r[i]; const char *txt = L->abase + r->off; int rc = rl_chars(txt, r->len);
            int a = c0 - cc; if (a < 0) a = 0; if (a > rc) a = rc;
            int b = c1 - cc; if (b < 0) b = 0; if (b > rc) b = rc;
            if (b > a) { int ba = rl_char_byte(txt, r->len, a), bb = rl_char_byte(txt, r->len, b); size_t add = (size_t)(bb - ba);
                if (len + add + 1 > cap) { while (len+add+1 > cap) cap = cap?cap*2:256; buf = realloc(buf, cap); }
                memcpy(buf + len, txt + ba, add); len += add; }
            cc += rc;
        }
        if (li < eLi) { if (len + 1 > cap) { cap = cap?cap*2:256; buf = realloc(buf, cap); } buf[len++] = '\n'; }
    }
    if (len) {
        clipboard_copy(buf, (int)len);
        int lines = eLi - sLi + 1;
        snprintf(g_toast, sizeof g_toast, "✓ copied %d line%s", lines, lines == 1 ? "" : "s");
        g_toast_until = now_ms() + 1500;
    }
    free(buf);
    g_sel = false; g_seldrag = false;
}
/* click in the input box → place the text cursor at the nearest cell (mirrors the input layout walk) */
static void input_click(int y, int x) {
    int row = g_in_top, col = 0, best = g_ilen;
    for (int i = 0; i <= g_ilen; ) {
        int base = (row == g_in_top) ? g_in_lm + 2 : g_in_lm;
        if (row == y && base + col >= x) { best = i; break; }   /* cursor goes before the clicked cell */
        if (row > y) { best = i; break; }                       /* clicked past the row's text */
        if (i >= g_ilen) { best = g_ilen; break; }
        unsigned char ch = (unsigned char)g_in[i];
        if (ch == '\n') { if (row == y) { best = i; break; } row++; col = 0; i++; continue; }
        int cl = (ch>=0xF0)?4:(ch>=0xE0)?3:(ch>=0xC0)?2:1; if (i+cl>g_ilen) cl = 1;
        i += cl; col++;
        if (base + col >= g_in_cw) { row++; col = 0; }
    }
    if (best < 0) best = 0;
    if (best > g_ilen) best = g_ilen;
    g_icur = best;
}
/* double-click in the transcript → select the word (alnum/_) under the cursor */
static void sel_word(int y, int x) {
    int li, col; bool inbody; sel_hit(y, x, &li, &col, &inbody);
    if (!inbody || g_nview == 0 || li >= g_nview) { g_sel = false; return; }
    RLine *L = g_view[li];
    char isw[1024]; int nchar = 0;
    for (int i = 0; i < L->n && nchar < 1024; i++) {
        const char *t = L->abase + L->r[i].off; int n = L->r[i].len;
        for (int b = 0; b < n && nchar < 1024; ) {
            unsigned char c = (unsigned char)t[b];
            int cl = (c>=0xF0)?4:(c>=0xE0)?3:(c>=0xC0)?2:1; if (b+cl>n) cl = 1;
            isw[nchar++] = (cl == 1 && (isalnum(c) || c == '_')) ? 1 : 0;
            b += cl;
        }
    }
    if (col < 0 || col >= nchar || !isw[col]) { g_sel = false; return; }
    int c0 = col, c1 = col + 1;
    while (c0 > 0 && isw[c0-1]) c0--;
    while (c1 < nchar && isw[c1]) c1++;
    g_sel = true; g_seldrag = false;
    g_sel_a_li = li; g_sel_a_col = c0; g_sel_c_li = li; g_sel_c_col = c1;
}
/* route a button-1 event: overlay row pick · input click-to-position · transcript select/word */
static void mouse_button1(const ncinput *ni) {
    if (ni->evtype == NCTYPE_PRESS) {
        long t = now_ms();
        int dy = ni->y - g_last_click_y, dx = ni->x - g_last_click_x;
        bool dbl = (t - g_last_click_ms < 400) && dy>=-1 && dy<=1 && dx>=-1 && dx<=1;
        g_last_click_ms = t; g_last_click_y = ni->y; g_last_click_x = ni->x;
        if (g_click_kind && ni->y >= 0 && ni->y < 1024 && g_click_row[ni->y] >= 0) {   /* overlay row → select */
            int idx = g_click_row[ni->y];
            switch (g_click_kind) { case 'm': g_msel=idx; break; case 'r': g_ssel=idx; break;
                                    case 'c': g_chsel=idx; break; case 'p': g_psel=idx; break; }
            g_sel = false; return;
        }
        if (g_resume_open || g_choice_open || g_confirm_quit || g_perm) { g_sel = false; return; }  /* modal up: ignore elsewhere */
        if (!g_rsearch && ni->y >= g_in_top && ni->y <= g_in_bot) { input_click(ni->y, ni->x); g_sel = false; return; }  /* input cursor */
        if (dbl) { sel_word(ni->y, ni->x); return; }   /* transcript word select */
        sel_mouse(ni);                                 /* begin a drag-selection */
        return;
    }
    sel_mouse(ni);                                     /* drag / release extend the selection */
}
/* Ctrl-C, claude-style staged: copy a selection · interrupt a running turn · back out of a draft ·
   only on an empty, idle prompt does it bring up the quit confirmation. */
static void ctrlc(void) {
    if (g_sel) { sel_copy(); return; }                       /* a selection exists → copy it */
    if (g_busy) { interrupt_turn(); return; }                /* turn running → stop it */
    if (g_ilen > 0 || g_nimg > 0) {                          /* a draft is present → clear it (back out) */
        in_clear(); menu_clear(); return;
    }
    g_confirm_quit = true; g_qsel = 0;                       /* empty + idle → exit confirmation */
}
static void on_key(uint32_t id, const ncinput *ni, bool more_after) {
    if (id == NCKEY_BUTTON1) { mouse_button1(ni); return; }   /* mouse: select / click-to-position / pick a row */
    if (ni->evtype == NCTYPE_RELEASE) return;
    if (id == NCKEY_RESIZE) { g_resized = true; return; }   /* global: modals must not swallow resize */
    bool ctrl = (ni->modifiers & NCKEY_MOD_CTRL) != 0;
    bool shift = (ni->modifiers & NCKEY_MOD_SHIFT) != 0;
    bool alt = (ni->modifiers & NCKEY_MOD_ALT) != 0;

    bool quitkey = (ctrl && (id=='c'||id=='C'||id=='d'||id=='D')) || id==0x03 || id==0x04;

    if (g_confirm_quit) {                            /* quit-confirmation modal swallows all keys */
        if (quitkey) { g_quit = true; return; }      /* second ctrl-c: force quit */
        if (id==NCKEY_UP||id==NCKEY_DOWN||id==NCKEY_LEFT||id==NCKEY_RIGHT||id==NCKEY_TAB) { g_qsel ^= 1; return; }
        if (id=='1'||id=='y'||id=='Y') { g_quit = true; return; }
        if (id=='2'||id=='n'||id=='N'||id==NCKEY_ESC) { g_confirm_quit = false; g_qsel = 0; return; }
        if (id==NCKEY_ENTER) { if (g_qsel == 0) g_quit = true; else { g_confirm_quit = false; g_qsel = 0; } return; }
        return;
    }
    if (g_resume_open) {                             /* session picker swallows keys */
        if (g_nsess == 0) { g_resume_open = false; return; }
        if (id==NCKEY_UP)                              { g_ssel = (g_ssel - 1 + g_nsess) % g_nsess; return; }
        if (id==NCKEY_DOWN || id==NCKEY_TAB)           { g_ssel = (g_ssel + 1) % g_nsess; return; }
        if (id==NCKEY_PGUP   || id==NCKEY_SCROLL_UP)   { g_ssel -= 5; if (g_ssel < 0) g_ssel = 0; return; }
        if (id==NCKEY_PGDOWN || id==NCKEY_SCROLL_DOWN) { g_ssel += 5; if (g_ssel >= g_nsess) g_ssel = g_nsess-1; return; }
        if (id==NCKEY_ENTER)                           { resume_session(g_ssel, false); return; }
        if (id=='f' || id=='F')                        { resume_session(g_ssel, true);  return; }  /* fork the selected session */
        if (id==NCKEY_ESC || quitkey)                  { g_resume_open = false; return; }
        return;
    }
    if (g_choice_open) {                             /* model / effort / rewind picker */
        if (g_nchoice == 0) { g_choice_open = false; return; }
        if (id==NCKEY_UP)                              { g_chsel = (g_chsel - 1 + g_nchoice) % g_nchoice; return; }
        if (id==NCKEY_DOWN || id==NCKEY_TAB)           { g_chsel = (g_chsel + 1) % g_nchoice; return; }
        if (id==NCKEY_PGUP   || id==NCKEY_SCROLL_UP)   { g_chsel -= 5; if (g_chsel < 0) g_chsel = 0; return; }
        if (id==NCKEY_PGDOWN || id==NCKEY_SCROLL_DOWN) { g_chsel += 5; if (g_chsel >= g_nchoice) g_chsel = g_nchoice-1; return; }
        if (id>='1' && id<='9') { int o = id - '1'; if (o < g_nchoice) { g_chsel = o; choice_apply(); } return; }
        if (id==NCKEY_ENTER)                           { choice_apply(); return; }
        if (id==NCKEY_ESC || quitkey)                  { g_choice_open = false; return; }
        return;
    }
    if ((ctrl && (id=='c'||id=='C')) || id==0x03) { ctrlc(); return; }   /* staged: copy sel / interrupt / clear draft / 2× to exit */
    if ((ctrl && (id=='d'||id=='D')) || id==0x04) {                      /* ctrl-d = EOF: exit only on an empty prompt */
        if (g_ilen == 0 && g_nimg == 0) g_quit = true;
        return;
    }

    if (g_perm) {                                     /* permission prompt: ONLY Enter answers — stray keystrokes can't grant */
        int plast = g_nopt + 1;
        if (id==NCKEY_UP)                         g_psel = (g_psel - 1 + plast + 1) % (plast + 1);
        else if (id==NCKEY_DOWN || id==NCKEY_TAB) g_psel = (g_psel + 1) % (plast + 1);
        else if (id>='1' && id<='9') { int o = id - '1'; if (o <= plast) g_psel = o; }   /* number highlights, does NOT confirm */
        else if (id==NCKEY_ENTER)                 answer_opt(g_psel);   /* the only key that answers/allows the option */
        else if (id==NCKEY_ESC)                   answer_opt(plast);    /* esc = deny (safe direction) */
        return;                                                          /* swallow every other key so typing can't answer */
    }

    if (g_rsearch) {                                 /* ctrl+r reverse history search */
        if (ctrl && (id=='r'||id=='R')) { rsearch_find(g_rmatch >= 0 ? g_rmatch - 1 : g_histn - 1); return; }
        if (id==NCKEY_ENTER) {                        /* accept the match into the input */
            if (g_rmatch >= 0) in_set(g_hist[g_rmatch]);
            g_rsearch = false; return;
        }
        if (id==NCKEY_ESC) { g_rsearch = false; return; }
        if (id==NCKEY_BACKSPACE) { if (g_rqlen > 0) g_rquery[--g_rqlen] = 0; rsearch_find(g_histn-1); return; }
        if (!ctrl && !alt && !nckey_synthesized_p(id) && id >= 0x20 && ni->utf8[0]) {
            int l = (int)strlen(ni->utf8);
            if (g_rqlen + l < (int)sizeof g_rquery - 1) { memcpy(g_rquery+g_rqlen, ni->utf8, (size_t)l); g_rqlen += l; g_rquery[g_rqlen] = 0; }
            rsearch_find(g_histn-1); return;
        }
        if (g_rmatch >= 0) in_set(g_hist[g_rmatch]);  /* any other key accepts, then is processed normally */
        g_rsearch = false;
    }

    if (id==NCKEY_TAB && shift) { cycle_mode(); return; }   /* cycle permission mode */

    if (g_menu) {                                    /* autocomplete navigation */
        if (id==NCKEY_TAB || id==NCKEY_DOWN) { g_msel = (g_msel+1)%g_nmatch; return; }
        if (id==NCKEY_UP) { g_msel = (g_msel-1+g_nmatch)%g_nmatch; return; }
        if (id==NCKEY_PGDOWN || id==NCKEY_SCROLL_DOWN) {   /* page / wheel down (clamped, no wrap) */
            g_msel += (id==NCKEY_PGDOWN) ? 10 : 3; if (g_msel >= g_nmatch) g_msel = g_nmatch-1; return; }
        if (id==NCKEY_PGUP || id==NCKEY_SCROLL_UP) {       /* page / wheel up */
            g_msel -= (id==NCKEY_PGUP) ? 10 : 3; if (g_msel < 0) g_msel = 0; return; }
        if (id==NCKEY_ENTER) {                             /* fully typed → run it; partial → complete */
            int tl = g_icur - g_tok_start;
            if (tl > 0 && (int)strlen(g_match[g_msel]) == tl && !strncmp(g_in + g_tok_start, g_match[g_msel], (size_t)tl)) {
                menu_clear(); submit_input(); menu_update();
            } else menu_accept();
            return;
        }
        if (id==NCKEY_ESC) { menu_clear(); return; }
    }

    if (g_vim && !g_vins) { vim_normal(id, ni); return; }   /* vim normal mode owns all keys */
    if (g_vim && g_vins && id == NCKEY_ESC) {               /* insert -> normal */
        g_vins = false; g_vop = 0; g_vcount = 0;
        if (g_icur > line_start(g_icur)) g_icur = utf8_prev(g_in, g_icur);
        return;
    }

    if (id == NCKEY_ESC) {                           /* stop the turn, or clear the draft */
        if (g_busy) { interrupt_turn(); return; }
        if (g_ilen) { in_clear(); menu_clear(); return; }
        return;
    }

    if (id == 0x1f || id == 0x1a) { undo_apply(); menu_update(); return; }   /* Ctrl+_ / Ctrl+Z: undo */
    if (ctrl && ((id>='a'&&id<='z')||(id>='A'&&id<='Z'))) {   /* readline-style editing (ASCII letters only) */
        char c = (id>='A'&&id<='Z') ? (char)(id-'A'+'a') : (char)id;
        switch (c) {
            case 'a': g_icur = line_start(g_icur); return;          /* line start */
            case 'e': g_icur = line_end(g_icur); return;            /* line end */
            case 'b': g_icur = utf8_prev(g_in, g_icur); return;     /* char back */
            case 'f': g_icur = utf8_next(g_in, g_icur, g_ilen); return; /* char fwd */
            case 'k': kill_to_eol(); menu_update(); return;         /* kill to eol */
            case 'u': kill_to_bol(); menu_update(); return;         /* kill to bol */
            case 'w': kill_word();   menu_update(); return;         /* kill word */
            case 'y': yank();        menu_update(); return;         /* yank */
            case 'j': in_insert("\n", 1); menu_update(); return;    /* newline (any terminal) */
            case 'l': g_resized = true; return;                     /* redraw */
            case 'o': g_expand = !g_expand; return;                 /* expand/collapse tool output */
            case 'p': cursor_up();   return;                        /* up / history */
            case 'n': cursor_down(); return;                        /* down / history */
            case 'v': paste_image(); menu_update(); return;         /* paste clipboard image */
            case 'r': if (g_histn) { g_rsearch = true; g_rqlen = 0; g_rquery[0] = 0; rsearch_find(g_histn-1); }
                      return;                                       /* reverse history search */
        }
    }
    if (alt) {                                       /* word motions */
        if (id=='b'||id=='B') { g_icur = word_left(g_icur);  return; }
        if (id=='f'||id=='F') { g_icur = word_right(g_icur); return; }
    }

    switch (id) {
        case NCKEY_ENTER:
            if (g_icur > 0 && g_in[g_icur-1] == '\\') { in_backspace(); in_insert("\n", 1); }  /* \+Enter */
            else if ((shift||alt) || more_after) in_insert("\n", 1);                            /* explicit/paste */
            else submit_input();
            menu_update(); return;
        case NCKEY_BACKSPACE: in_backspace(); menu_update(); return;
        case NCKEY_DEL: in_delete(); menu_update(); return;
        case NCKEY_LEFT:  g_icur = utf8_prev(g_in, g_icur); menu_update(); return;
        case NCKEY_RIGHT: g_icur = utf8_next(g_in, g_icur, g_ilen); menu_update(); return;
        case NCKEY_HOME:  g_icur = line_start(g_icur); return;
        case NCKEY_END:   g_icur = line_end(g_icur); return;
        case NCKEY_UP:   cursor_up();   return;
        case NCKEY_DOWN: cursor_down(); return;
        case NCKEY_PGUP:   g_scroll += 5; return;
        case NCKEY_PGDOWN: g_scroll -= 5; if (g_scroll<0) g_scroll=0; return;
        case NCKEY_TAB: if (g_menu) { menu_accept(); } return;
        case NCKEY_RESIZE: g_resized = true; return;
        default: break;
    }
    if (id==NCKEY_SCROLL_UP) { g_scroll += 3; return; }
    if (id==NCKEY_SCROLL_DOWN) { g_scroll -= 3; if (g_scroll<0) g_scroll=0; return; }

    if (!nckey_synthesized_p(id) && id >= 0x20 && ni->utf8[0]) {
        in_insert(ni->utf8, (int)strlen(ni->utf8)); menu_update();
    }
}

/* ====================================================== engine =========== */
static int spawn_engine(const char *resume_id, bool forked) {
    const char *bin = g_bin[0] ? g_bin : getenv("CRUD_CLAUDE_BIN"); if (!bin) bin = DEFAULT_BIN;
    const char *model = g_model_arg[0] ? g_model_arg : NULL;   /* set via /model (or CRUD_MODEL at startup) */
    const char *effort = g_effort[0] ? g_effort : NULL;        /* set via /effort */
    int to[2], from[2]; if (pipe(to) || pipe(from)) { perror("pipe"); return -1; }
    g_child = fork(); if (g_child < 0) { perror("fork"); return -1; }
    if (g_child == 0) {
        prctl(PR_SET_PDEATHSIG, SIGKILL);     /* engine dies instantly if crud-cli dies */
        dup2(to[0], STDIN_FILENO); dup2(from[1], STDOUT_FILENO);
        int dn = open("/dev/null", O_WRONLY); if (dn>=0) dup2(dn, STDERR_FILENO);
        close(to[0]); close(to[1]); close(from[0]); close(from[1]);
        unsetenv("ANTHROPIC_API_KEY");        /* clear API-key env so the child uses the logged-in CLI session */
        unsetenv("ANTHROPIC_AUTH_TOKEN");
        char *av[64]; int a = 0;
        av[a++]=(char*)bin; av[a++]="-p"; av[a++]="--verbose";
        av[a++]="--input-format"; av[a++]="stream-json";
        av[a++]="--output-format"; av[a++]="stream-json";
        av[a++]="--include-partial-messages";
        av[a++]="--permission-mode"; av[a++]= g_permmode[0] ? g_permmode : "default";
        av[a++]="--permission-prompt-tool"; av[a++]="stdio";
        if (resume_id && *resume_id) { av[a++]="--resume"; av[a++]=(char*)resume_id;
            if (forked) av[a++]="--fork-session"; }   /* branch into a NEW session seeded from this one */
        if (model && *model)   { av[a++]="--model";  av[a++]=(char*)model; }
        if (effort && *effort) { av[a++]="--effort"; av[a++]=(char*)effort; }
        if (g_agent_arg[0])    { av[a++]="--agent";  av[a++]=g_agent_arg; }
        for (int i = 0; i < g_nadddir; i++) { av[a++]="--add-dir"; av[a++]=g_adddir[i]; }   /* last: one flag per dir */
        av[a]=NULL; execvp(bin, av); perror("execvp"); _exit(127);   /* execvp: searches PATH when bin has no slash */
    }
    close(to[0]); close(from[1]); g_wfd = to[1];
    fcntl(from[0], F_SETFL, O_NONBLOCK); g_efd = from[0]; return from[0];
}
/* hard-restart the engine (kill the exact child PID we forked — never pattern-match), optionally
   resuming a stored session. Re-handshakes and clears volatile per-turn state. */
static void restart_engine(const char *resume_id, bool forked) {
    if (g_wfd >= 0) { close(g_wfd); g_wfd = -1; }
    if (g_child > 0) { kill(g_child, SIGKILL); int st; waitpid(g_child, &st, 0); g_child = -1; }
    g_accl = 0;                                       /* drop any partial line from the dead engine */
    if (spawn_engine(resume_id, forked) < 0) { g_engine_alive = false; return; }
    g_engine_alive = true;
    char buf[160]; snprintf(buf, sizeof buf,
        "{\"type\":\"control_request\",\"request_id\":\"%s\",\"request\":{\"subtype\":\"initialize\",\"hooks\":{}}}", INIT_ID);
    send_line(buf);
    g_busy = false; g_perm = false; g_perm_isplan = false;
    for (int i = 0; i < g_nqueue; i++) free(g_queue[i]);
    g_nqueue = 0;
    snprintf(g_status, sizeof g_status, "idle");
}

/* ---- background plan-usage fetch (via curl; token never on argv) ---- */
static long parse_iso(const char *s) {     /* "YYYY-MM-DDTHH:MM:SS…+00:00" (UTC) -> unix time */
    struct tm tm; memset(&tm, 0, sizeof tm);
    if (sscanf(s, "%d-%d-%dT%d:%d:%d", &tm.tm_year, &tm.tm_mon, &tm.tm_mday, &tm.tm_hour, &tm.tm_min, &tm.tm_sec) != 6) return 0;
    tm.tm_year -= 1900; tm.tm_mon -= 1;
    return (long)timegm(&tm);
}
/* load last-known usage from the shared cache; returns 1 if it's still fresh (< max_age sec) */
static int usage_cache_fresh(const char *path, int max_age) {
    FILE *f = fopen(path, "r"); if (!f) return 0;
    double u5 = -1, u7 = -1; long u5r = 0, u7r = 0, ts = 0; int fresh = 0;
    if (fscanf(f, "%lf %lf %ld %ld %ld", &u5, &u7, &u5r, &u7r, &ts) == 5 && u5 >= 0) {
        g_u5 = u5; g_u7 = u7; g_u5r = u5r; g_u7r = u7r;          /* always show last-known, even if stale */
        if ((long)time(NULL) - ts < max_age) fresh = 1;
    }
    fclose(f); return fresh;
}
static void *usage_thread(void *arg) {
    (void)arg;
    const char *h = getenv("HOME");
    char credp[320]; snprintf(credp, sizeof credp, "%s/.claude/.credentials.json", h ? h : "");
    char hdrp[64];   snprintf(hdrp, sizeof hdrp, "/tmp/crud-uh-%d", (int)getpid());
    char cache[64];  snprintf(cache, sizeof cache, "/tmp/crud-usage-%d", (int)getuid());
    int backoff = 0;                                  /* loops to wait after a rate-limit/error */
    while (!g_quit) {
        if (!usage_cache_fresh(cache, 240) && backoff <= 0) {   /* fetch only if cache stale & not backing off */
            FILE *cf = fopen(credp, "rb");
            if (cf) {
                char buf[16384]; size_t n = fread(buf, 1, sizeof buf - 1, cf); buf[n] = 0; fclose(cf);
                char *tok = j_str(buf, "accessToken");
                if (tok) {
                    int fd = open(hdrp, O_WRONLY | O_CREAT | O_TRUNC, 0600);   /* 0600: token readable only by us */
                    if (fd >= 0) {
                        dprintf(fd, "Authorization: Bearer %s\n", tok); close(fd);
                        char cmd[256]; snprintf(cmd, sizeof cmd,
                            "curl -s --max-time 12 -H @%s -H 'anthropic-beta: oauth-2025-04-20' "
                            "-H 'Content-Type: application/json' '%s'", hdrp, USAGE_URL);
                        FILE *pp = popen(cmd, "r");
                        if (pp) {
                            char out[16384]; size_t on = fread(out, 1, sizeof out - 1, pp); out[on] = 0; pclose(pp);
                            const char *f5 = strstr(out, "\"five_hour\"");
                            const char *f7 = strstr(out, "\"seven_day\"");
                            if (f5) {
                                g_u5 = j_num(f5, "utilization"); char *r = j_str(f5, "resets_at"); if (r) { g_u5r = parse_iso(r); free(r); }
                                if (f7) { g_u7 = j_num(f7, "utilization"); char *r2 = j_str(f7, "resets_at"); if (r2) { g_u7r = parse_iso(r2); free(r2); } }
                                FILE *wc = fopen(cache, "w");
                                if (wc) { fprintf(wc, "%.1f %.1f %ld %ld %ld\n", g_u5, g_u7, g_u5r, g_u7r, (long)time(NULL)); fclose(wc); }
                                backoff = 0;
                            } else backoff = 10;        /* rate-limited / error -> wait ~10 min before retrying */
                        }
                        unlink(hdrp);
                    }
                    free(tok);
                }
            }
        }
        if (backoff > 0) backoff--;
        for (int i = 0; i < 60 && !g_quit; i++) sleep(1);
    }
    return NULL;
}

/* ctrl-c arrives as SIGINT (notcurses' own quit handlers are disabled below), so route it through a
   flag the main loop turns into the confirm modal; TERM/QUIT quit gracefully so the terminal restores. */
static void on_signal(int s) { if (s == SIGINT) g_sigint = 1; else g_sigterm = 1; }

int main(int argc, char **argv) {
    setlocale(LC_ALL, ""); signal(SIGPIPE, SIG_IGN);
    signal(SIGINT, on_signal); signal(SIGTERM, on_signal); signal(SIGQUIT, on_signal);
    seed_builtin_cmds();                    /* client-side commands available before init */
    if (getcwd(g_cwd, sizeof g_cwd) == NULL) g_cwd[0] = 0;   /* needed before resolving a session to resume */

    /* CLI flags — parity with `claude`; these also replace the CRUD_MODEL / CRUD_CLAUDE_BIN env vars */
    bool want_resume = false, want_continue = false; const char *resume_arg = NULL;
    bool cli_model = false; char promptbuf[8192]; promptbuf[0] = 0;
    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        const char *val = (i + 1 < argc) ? argv[i+1] : NULL;   /* next token, for value-taking flags */
        if (!strcmp(a, "--continue") || !strcmp(a, "-c")) want_continue = true;
        else if (!strcmp(a, "--resume") || !strcmp(a, "-r")) {
            want_resume = true;
            if (i + 1 < argc && argv[i+1][0] != '-') resume_arg = argv[++i];
        }
        else if (!strcmp(a, "--model")  && val) { i++; if (valid_model(val)) { snprintf(g_model_arg, sizeof g_model_arg, "%s", strcmp(val,"default")?val:""); cli_model = true; } }
        else if (!strcmp(a, "--effort") && val) { i++; if (valid_effort(val)) snprintf(g_effort, sizeof g_effort, "%s", val); }
        else if (!strcmp(a, "--permission-mode") && val) { i++; snprintf(g_permmode, sizeof g_permmode, "%s", val); }
        else if ((!strcmp(a, "--name") || !strcmp(a, "-n")) && val) { i++; snprintf(g_pending_name, sizeof g_pending_name, "%s", val); }
        else if ((!strcmp(a, "--claude-bin") || !strcmp(a, "--bin")) && val) { i++; snprintf(g_bin, sizeof g_bin, "%s", val); }
        else if (!strcmp(a, "--agent")  && val) { i++; snprintf(g_agent_arg, sizeof g_agent_arg, "%s", val); }
        else if (!strcmp(a, "--add-dir")) { while (i + 1 < argc && argv[i+1][0] != '-' && g_nadddir < 8) snprintf(g_adddir[g_nadddir++], 512, "%s", argv[++i]); }
        else if (!strcmp(a, "--help") || !strcmp(a, "-h")) {
            fprintf(stderr, "crud-cli — notcurses front end for Claude Code\n"
                "usage: crud-cli [options] [prompt]\n"
                "  -c, --continue           resume the most recent session here\n"
                "  -r, --resume [name|id]   resume a named/id session (no arg: pick from a list)\n"
                "  -n, --name <name>        name this session (shown in the /resume picker)\n"
                "      --model <m>          model alias (default opus sonnet haiku opus[1m] …)\n"
                "      --effort <level>     low | medium | high | xhigh | max\n"
                "      --permission-mode <m> default | acceptEdits | plan | bypassPermissions\n"
                "      --agent <agent>      session agent\n"
                "      --add-dir <dirs...>  extra directories the engine may access\n"
                "      --claude-bin <path>  engine binary (else $CRUD_CLAUDE_BIN, else `claude`)\n"
                "  [prompt]                 send this as the first message on launch\n");
            return 0;
        }
        else if (a[0] != '-') {                                 /* positional → initial prompt (space-joined) */
            size_t pl = strlen(promptbuf);
            if (pl) { strncat(promptbuf, " ", sizeof promptbuf - pl - 1); pl++; }
            strncat(promptbuf, a, sizeof promptbuf - pl - 1);
        }
        /* unknown --flags are ignored (crud-cli is a front-end, not a full claude arg passthrough) */
    }
    char start_id[64] = ""; bool start_loaded = false, start_pick = false;
    if (want_continue || want_resume) {
        populate_sessions();                                 /* newest first */
        int hit = -1;
        if (want_continue) { if (g_nsess > 0) hit = 0; }
        else if (resume_arg) {                               /* exact name → id-prefix → name-substring */
            for (int i = 0; i < g_nsess && hit < 0; i++) if (g_sess[i].name[0] && !strcasecmp(g_sess[i].name, resume_arg)) hit = i;
            for (int i = 0; i < g_nsess && hit < 0; i++) if (!strncmp(g_sess[i].id, resume_arg, strlen(resume_arg))) hit = i;
            for (int i = 0; i < g_nsess && hit < 0; i++) if (g_sess[i].name[0] && ci_strstr(g_sess[i].name, resume_arg)) hit = i;
        } else start_pick = (g_nsess > 0);                   /* --resume with no arg → open the picker after init */
        if (hit >= 0) { load_transcript(g_sess[hit].path);
            snprintf(start_id, sizeof start_id, "%s", g_sess[hit].id);
            snprintf(g_sid, sizeof g_sid, "%s", g_sess[hit].id);
            snprintf(g_session, sizeof g_session, "%.8s", g_sess[hit].id); start_loaded = true; }
    }

    if (spawn_engine(start_id[0] ? start_id : NULL, false) < 0) return 1;
    { char buf[160]; snprintf(buf, sizeof buf,
        "{\"type\":\"control_request\",\"request_id\":\"%s\","
        "\"request\":{\"subtype\":\"initialize\",\"hooks\":{}}}", INIT_ID); send_line(buf); }
    /* show identity on launch — system/init only arrives on the first turn, so pre-seed from cache */
    ident_load();                                   /* model/plan/version from the last session */
    { const char *m = getenv("CRUD_MODEL"); if (m && *m && !cli_model) { snprintf(g_model, sizeof g_model, "%s", m); snprintf(g_model_arg, sizeof g_model_arg, "%s", m); }
      if (cli_model) snprintf(g_model, sizeof g_model, "%s", g_model_arg[0] ? g_model_arg : "default");   /* CLI --model wins the pre-init display */
      if (!g_version[0]) { const char *bin = g_bin[0] ? g_bin : getenv("CRUD_CLAUDE_BIN"); if (!bin) bin = DEFAULT_BIN;
          const char *v = strrchr(bin, '/'); snprintf(g_version, sizeof g_version, "%.63s", v ? v+1 : bin); } }

    notcurses_options opts; memset(&opts, 0, sizeof opts);
    opts.flags = NCOPTION_SUPPRESS_BANNERS | NCOPTION_INHIBIT_SETLOCALE | NCOPTION_NO_QUIT_SIGHANDLERS;
    g_nc = notcurses_core_init(&opts, NULL);
    if (!g_nc) { fprintf(stderr, "notcurses init failed (need a real terminal)\n");
        if (g_wfd>=0) close(g_wfd);
        if (g_child>0){ kill(g_child,SIGTERM); int s; waitpid(g_child,&s,0); }
        return 1; }
    g_std = notcurses_stdplane(g_nc);
    notcurses_mice_enable(g_nc, NCMICE_BUTTON_EVENT | NCMICE_DRAG_EVENT);   /* button + drag → in-app selection; wheel still scrolls */
    notcurses_cursor_disable(g_nc);   /* we draw our own block cursor; keep the hardware cursor off so renders never toggle it */
    pthread_t ut; pthread_create(&ut, NULL, usage_thread, NULL); pthread_detach(ut);   /* plan-usage poller */

    if (start_loaded) {                              /* resumed a session from the command line */
        int b = blk_new(B_SYS); char m[96]; char nm[140]; session_name_get(start_id, nm, sizeof nm);
        if (nm[0]) snprintf(m, sizeof m, "\xe2\x9c\xa6 resumed \xe2\x80\x9c%.60s\xe2\x80\x9d (%.8s)", nm, start_id);
        else       snprintf(m, sizeof m, "\xe2\x9c\xa6 resumed session %.8s", start_id);
        blk_str(b, m); g_scroll = 0;
    } else if (start_pick) { g_resume_open = true; g_ssel = 0; }   /* --resume with no arg: pick at startup */
    else if (want_resume && resume_arg) {                          /* named resume didn't match → say so, start fresh */
        int b = blk_new(B_SYS); char m[160]; snprintf(m, sizeof m, "no session named or starting with \xe2\x80\x9c%.60s\xe2\x80\x9d — started a fresh session", resume_arg);
        blk_str(b, m); g_scroll = 0;
    }
    if (promptbuf[0] && !start_pick) {              /* positional [prompt] → send it as the first message */
        int b = blk_new(B_USER); blk_str(b, promptbuf);
        if (g_histn < 256) g_hist[g_histn++] = strdup(promptbuf);
        g_histpos = g_histn;
        dispatch_user(promptbuf);
    }

    char rbuf[65536];
    struct timespec zero = { 0, 0 };
    render();
    while (!g_quit) {
        struct pollfd pfd[2];
        pfd[0].fd = g_engine_alive ? g_efd : -1; pfd[0].events = POLLIN;  /* -1 ⇒ ignored: a dead pipe must not busy-loop on POLLHUP */
        pfd[1].fd = notcurses_inputready_fd(g_nc); pfd[1].events = POLLIN;
        int pr = poll(pfd, 2, 100); bool dirty = false;

        if (pr > 0 && (pfd[0].revents & (POLLIN|POLLHUP))) {
            ssize_t got;
            while ((got = read(g_efd, rbuf, sizeof rbuf)) > 0) {
                if (g_accl + (size_t)got + 1 > g_acccap) { while (g_accl+(size_t)got+1 > g_acccap) g_acccap = g_acccap?g_acccap*2:65536; g_acc = realloc(g_acc, g_acccap); }
                memcpy(g_acc + g_accl, rbuf, (size_t)got); g_accl += (size_t)got;
                size_t st = 0;
                for (size_t i = 0; i < g_accl; i++) if (g_acc[i]=='\n') { g_acc[i]=0; if (i>st) on_line(g_acc+st); st=i+1; }
                if (st > 0) { memmove(g_acc, g_acc+st, g_accl-st); g_accl -= st; }
                dirty = true;
            }
            if (got == 0) { g_engine_alive = false; dirty = true; }
        }

        /* drain input as a burst so we can tell paste-newlines from a lone Enter */
        ncinput burst[512]; int bn = 0; ncinput ni; uint32_t id;
        while (bn < 512 && (id = notcurses_get(g_nc, &zero, &ni)) > 0) {
            if (id == (uint32_t)-1) break;
            ni.id = id; burst[bn++] = ni;
        }
        /* "more_after" tells Enter whether it's a paste-newline (more text follows) vs a submit.
           Only a real following character or Enter counts — release events (kitty protocol), mouse,
           resize and navigation keys must NOT, or a lone Enter batched with them silently becomes a
           newline and the prompt never submits (the "typed while busy, got lost" bug). */
        for (int i = 0; i < bn; i++) {
            bool more = false;
            for (int j = i + 1; j < bn; j++) {
                if (burst[j].evtype == NCTYPE_RELEASE) continue;
                uint32_t jid = burst[j].id;
                if (jid == NCKEY_ENTER || (!nckey_synthesized_p(jid) && jid >= 0x20)) { more = true; break; }
            }
            on_key(burst[i].id, &burst[i], more); dirty = true;
        }

        if (g_sigterm) g_quit = true;        /* SIGTERM/SIGQUIT: graceful exit */
        if (g_sigint) {                      /* ctrl-c arriving as a signal (cooked tty) → same staged handling as the key */
            g_sigint = 0;
            if (g_confirm_quit) g_quit = true;   /* a typed /quit modal is up → confirm it */
            else ctrlc();
            dirty = true;
        }
        /* Animate the working spinner off the wall clock: only repaint when its visible phase
           (glyph + elapsed second) actually changes, so a stationary screen never redraws. */
        if (g_busy && !g_perm) {
            long ph = ((long)time(NULL) - g_turn_start) * 6 + (now_ms() / 280) % 6;
            if (ph != g_spin_phase) { g_spin_phase = ph; dirty = true; }
        }
        if (g_toast_until && now_ms() >= g_toast_until) { g_toast_until = 0; dirty = true; }   /* expire the footer toast */
        if (g_seldrag && (g_drag_y < g_v_hdr || g_drag_y >= g_v_hdr + g_v_body)) {   /* drag past edge → auto-scroll */
            if (g_drag_y < g_v_hdr) { g_scroll += 2; g_sel_c_li = g_v_first; g_sel_c_col = 0; }
            else { g_scroll -= 2; if (g_scroll < 0) g_scroll = 0;
                   int last = g_v_first + g_v_body - 1; if (last < 0) last = 0; if (last >= g_nview) last = g_nview - 1;
                   g_sel_c_li = last; g_sel_c_col = (g_nview && last < g_nview) ? rline_width(g_view[last]) : 0; }
            dirty = true;
        }
        if (dirty) render();
    }
    { ssize_t w = write(STDOUT_FILENO, "\033[0 q", 5); (void)w; }   /* restore the terminal's default cursor */
    notcurses_stop(g_nc);
    if (g_wfd >= 0) close(g_wfd);
    if (g_child > 0) { int s; waitpid(g_child, &s, 0); }
    free(g_acc);
    return 0;
}
