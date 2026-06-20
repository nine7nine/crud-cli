/* json.c — see json.h. Minimal field scanners over the engine's JSONL frames. */
#define _GNU_SOURCE
#include "json.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const char *j_obj_end(const char *start) {
    const char *p = start; int d = 0, instr = 0;
    for (; *p; p++) {
        if (instr) { if (*p=='\\') { if (p[1]) p++; } else if (*p=='"') instr = 0; }
        else if (*p=='"') instr = 1;
        else if (*p=='{') d++;
        else if (*p=='}') { if (--d == 0) { p++; break; } }
    }
    return p;
}
char *j_str(const char *s, const char *key) {
    char pat[96]; snprintf(pat, sizeof pat, "\"%s\"", key);
    const char *p = strstr(s, pat); if (!p) return NULL;
    p += strlen(pat); while (*p == ' ' || *p == ':') p++;
    if (*p != '"') return NULL;
    p++;
    const char *st = p; while (*p && !(*p == '"' && p[-1] != '\\')) p++;
    size_t n = (size_t)(p - st); char *o = malloc(n + 1); if (!o) return NULL;
    memcpy(o, st, n); o[n] = 0; return o;
}

double j_num(const char *s, const char *key) {
    char pat[96]; snprintf(pat, sizeof pat, "\"%s\"", key);
    const char *p = strstr(s, pat); if (!p) return 0;
    p += strlen(pat); while (*p == ' ' || *p == ':') p++; return strtod(p, NULL);
}

char *j_obj(const char *s, const char *key) {
    char pat[96]; snprintf(pat, sizeof pat, "\"%s\"", key);
    const char *p = strstr(s, pat); if (!p) return NULL;
    p += strlen(pat); while (*p == ' ' || *p == ':') p++;
    if (*p != '{') return NULL;
    const char *st = p; int d = 0, instr = 0;
    for (; *p; p++) {
        if (instr) { if (*p == '\\') { if (p[1]) p++; } else if (*p == '"') instr = 0; }
        else if (*p == '"') instr = 1;
        else if (*p == '{') d++;
        else if (*p == '}') { if (--d == 0) { p++; break; } }
    }
    size_t n = (size_t)(p - st); char *o = malloc(n + 1); if (!o) return NULL;
    memcpy(o, st, n); o[n] = 0; return o;
}

char *j_arr(const char *s, const char *key) {
    char pat[96]; snprintf(pat, sizeof pat, "\"%s\"", key);
    const char *p = strstr(s, pat); if (!p) return NULL;
    p += strlen(pat); while (*p == ' ' || *p == ':') p++;
    if (*p != '[') return NULL;
    const char *st = p; int d = 0, instr = 0;
    for (; *p; p++) {
        if (instr) { if (*p == '\\') { if (p[1]) p++; } else if (*p == '"') instr = 0; }
        else if (*p == '"') instr = 1;
        else if (*p == '[') d++;
        else if (*p == ']') { if (--d == 0) { p++; break; } }
    }
    size_t n = (size_t)(p - st); char *o = malloc(n + 1); if (!o) return NULL;
    memcpy(o, st, n); o[n] = 0; return o;
}

char *j_escape(const char *src) {
    size_t n = strlen(src); char *o = malloc(n * 6 + 1); if (!o) return NULL;
    char *w = o;
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)src[i];
        switch (c) {
            case '"':  *w++='\\'; *w++='"';  break;
            case '\\': *w++='\\'; *w++='\\'; break;
            case '\n': *w++='\\'; *w++='n';  break;
            case '\r': *w++='\\'; *w++='r';  break;
            case '\t': *w++='\\'; *w++='t';  break;
            default: if (c < 0x20) w += sprintf(w, "\\u%04x", c); else *w++ = (char)c;
        }
    }
    *w = 0; return o;
}

char *j_unescape_dup(const char *s) {
    size_t n = strlen(s); char *o = malloc(n + 1); if (!o) return NULL; char *w = o;
    for (const char *p = s; *p; p++) {
        if (*p == '\\' && p[1]) {
            p++;
            switch (*p) {
                case 'n': *w++='\n'; break;  case 't': *w++='\t'; break;
                case 'r': break;             case '"': *w++='"'; break;
                case '\\': *w++='\\'; break;  case '/': *w++='/'; break;
                case 'u': {
                    if (p[1]&&p[2]&&p[3]&&p[4]) {
                        char hx[5]={p[1],p[2],p[3],p[4],0}; unsigned cp=(unsigned)strtol(hx,NULL,16);
                        if (cp<0x80) *w++=(char)cp;
                        else if (cp<0x800){*w++=(char)(0xC0|cp>>6);*w++=(char)(0x80|(cp&0x3F));}
                        else {*w++=(char)(0xE0|cp>>12);*w++=(char)(0x80|((cp>>6)&0x3F));*w++=(char)(0x80|(cp&0x3F));}
                        p += 4;
                    }
                    break;
                }
                default: *w++ = *p;
            }
        } else *w++ = *p;
    }
    *w = 0; return o;
}
