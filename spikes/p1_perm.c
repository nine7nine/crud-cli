/*
 * p1_perm.c — P1 spike: prove the Claude Code headless permission control protocol.
 *
 * Goal: drive the `claude` binary over plain pipes (NO PTY) in stream-json mode,
 *       send the `initialize` control handshake so WE become the permission host,
 *       trigger a permission-gated tool (Write), receive the `can_use_tool`
 *       control_request, and answer it (allow/deny) via a control_response.
 *
 * Safety: NO --dangerously-skip-permissions, NO bypass modes. A 60s alarm kills
 *         the child and exits so this can never hang and chew resources.
 *
 * Usage:  ./p1_perm [allow|deny]   (default: allow)
 *
 * Build:  cc -O2 -Wall -Wextra -o p1_perm p1_perm.c
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <sys/types.h>

static const char *CLAUDE_BIN =
    "/home/ninez/.local/share/claude/versions/2.1.169";
static const char *MODEL    = "claude-haiku-4-5-20251001";
static const char *WORKDIR  = "/tmp";
static const char *INIT_ID  = "p1-init-1";

/* The prompt is plain ASCII (no chars needing JSON escaping). */
static const char *PROMPT =
    "Use the Write tool to create a file named p1_spike.txt "
    "containing the text hello-from-p1. Then stop.";

static pid_t g_child = -1;

static void on_alarm(int sig) {
    (void)sig;
    const char *m = "\n[p1] TIMEOUT (60s) — killing child and exiting.\n";
    if (write(2, m, strlen(m)) < 0) { /* ignore */ }
    if (g_child > 0) kill(g_child, SIGKILL);
    _exit(124);
}

/* write a full JSON line + newline to fd (no stdio buffering games) */
static void send_line(int fd, const char *json) {
    size_t n = strlen(json);
    (void)(write(fd, json, n) + write(fd, "\n", 1));
    fprintf(stderr, ">> %s\n", json);
}

/* Find "key":"value" and return malloc'd value (no escape decoding — fine for
 * uuids / simple ids). Returns NULL if not found. Searches the WHOLE line, so
 * it grabs the first occurrence of the key. */
static char *json_str(const char *s, const char *key) {
    char pat[128];
    snprintf(pat, sizeof pat, "\"%s\"", key);
    const char *p = strstr(s, pat);
    if (!p) return NULL;
    p += strlen(pat);
    while (*p == ' ' || *p == ':' ) p++;
    if (*p != '"') return NULL;
    p++;
    const char *start = p;
    while (*p && !(*p == '"' && p[-1] != '\\')) p++;
    size_t len = (size_t)(p - start);
    char *out = malloc(len + 1);
    if (!out) return NULL;
    memcpy(out, start, len);
    out[len] = '\0';
    return out;
}

/* Extract the raw object value after "key": by brace-matching (string-aware).
 * Returns malloc'd "{...}" or NULL. Used to echo `input` back as updatedInput. */
static char *json_raw_obj(const char *s, const char *key) {
    char pat[128];
    snprintf(pat, sizeof pat, "\"%s\"", key);
    const char *p = strstr(s, pat);
    if (!p) return NULL;
    p += strlen(pat);
    while (*p == ' ' || *p == ':') p++;
    if (*p != '{') return NULL;
    const char *start = p;
    int depth = 0, instr = 0;
    for (; *p; p++) {
        if (instr) {
            if (*p == '\\') { if (p[1]) p++; }
            else if (*p == '"') instr = 0;
        } else if (*p == '"') instr = 1;
        else if (*p == '{') depth++;
        else if (*p == '}') { if (--depth == 0) { p++; break; } }
    }
    size_t len = (size_t)(p - start);
    char *out = malloc(len + 1);
    if (!out) return NULL;
    memcpy(out, start, len);
    out[len] = '\0';
    return out;
}

int main(int argc, char **argv) {
    int do_allow = 1;
    if (argc > 1 && strcmp(argv[1], "deny") == 0) do_allow = 0;
    fprintf(stderr, "[p1] decision = %s\n", do_allow ? "ALLOW" : "DENY");

    int to_child[2], from_child[2];      /* to_child: we write; from_child: we read */
    if (pipe(to_child) || pipe(from_child)) { perror("pipe"); return 1; }

    g_child = fork();
    if (g_child < 0) { perror("fork"); return 1; }

    if (g_child == 0) {
        /* CHILD: wire pipes to stdin/stdout, keep stderr, exec the engine. */
        dup2(to_child[0],   STDIN_FILENO);
        dup2(from_child[1], STDOUT_FILENO);
        close(to_child[0]);  close(to_child[1]);
        close(from_child[0]); close(from_child[1]);
        if (chdir(WORKDIR) != 0) perror("chdir");
        char *argv2[24];
        int a = 0;
        argv2[a++] = (char*)CLAUDE_BIN;
        argv2[a++] = "-p";
        argv2[a++] = "--model";        argv2[a++] = (char*)MODEL;
        argv2[a++] = "--verbose";
        argv2[a++] = "--input-format";  argv2[a++] = "stream-json";
        argv2[a++] = "--output-format"; argv2[a++] = "stream-json";
        argv2[a++] = "--permission-mode"; argv2[a++] = "default";  /* NO bypass */
        const char *ppt = getenv("CC_PPT");                 /* probe: --permission-prompt-tool */
        if (ppt && *ppt) { argv2[a++] = "--permission-prompt-tool"; argv2[a++] = (char*)ppt; }
        argv2[a] = NULL;
        execv(CLAUDE_BIN, argv2);
        perror("execv");
        _exit(127);
    }

    /* PARENT */
    close(to_child[0]);
    close(from_child[1]);
    int wfd = to_child[1];
    FILE *rf = fdopen(from_child[0], "r");
    if (!rf) { perror("fdopen"); return 1; }
    FILE *raw = fopen("/tmp/p1_raw.jsonl", "w");   /* full transcript for diagnosis */

    signal(SIGALRM, on_alarm);
    alarm(60);

    /* 1) initialize handshake — declares us as the SDK/permission host. */
    {
        char buf[256];
        snprintf(buf, sizeof buf,
            "{\"type\":\"control_request\",\"request_id\":\"%s\","
            "\"request\":{\"subtype\":\"initialize\",\"hooks\":{}}}", INIT_ID);
        send_line(wfd, buf);
    }

    int user_sent = 0, perm_seen = 0;
    char *line = NULL;
    size_t cap = 0;
    ssize_t n;

    while ((n = getline(&line, &cap, rf)) != -1) {
        if (raw) { fwrite(line, 1, (size_t)n, raw); fflush(raw); }
        if (n <= 1) continue;                       /* blank */
        char *type = json_str(line, "type");
        if (!type) { free(type); continue; }

        if (strcmp(type, "control_response") == 0) {
            char *rid = json_str(line, "request_id");
            fprintf(stderr, "<< control_response (request_id=%s)\n",
                    rid ? rid : "?");
            /* init ack -> now send the user turn */
            if (!user_sent && rid && strcmp(rid, INIT_ID) == 0) {
                char msg[512];
                snprintf(msg, sizeof msg,
                    "{\"type\":\"user\",\"message\":{\"role\":\"user\","
                    "\"content\":\"%s\"}}", PROMPT);
                send_line(wfd, msg);
                user_sent = 1;
            }
            free(rid);
        }
        else if (strcmp(type, "control_request") == 0) {
            char *sub = json_str(line, "subtype");
            if (sub && strcmp(sub, "can_use_tool") == 0) {
                perm_seen = 1;
                char *rid   = json_str(line, "request_id");
                char *tname = json_str(line, "tool_name");
                char *input = json_raw_obj(line, "input");
                fprintf(stderr,
                    "\n<< ===== can_use_tool =====\n"
                    "   request_id = %s\n   tool_name  = %s\n   input      = %s\n",
                    rid ? rid : "?", tname ? tname : "?",
                    input ? input : "?");

                char resp[4096];
                if (do_allow) {
                    snprintf(resp, sizeof resp,
                        "{\"type\":\"control_response\",\"response\":{"
                        "\"subtype\":\"success\",\"request_id\":\"%s\","
                        "\"response\":{\"behavior\":\"allow\",\"updatedInput\":%s}}}",
                        rid ? rid : "", input ? input : "{}");
                } else {
                    snprintf(resp, sizeof resp,
                        "{\"type\":\"control_response\",\"response\":{"
                        "\"subtype\":\"success\",\"request_id\":\"%s\","
                        "\"response\":{\"behavior\":\"deny\","
                        "\"message\":\"P1 spike: denied by host\"}}}",
                        rid ? rid : "");
                }
                send_line(wfd, resp);
                free(rid); free(tname); free(input);
            }
            free(sub);
        }
        else if (strcmp(type, "result") == 0) {
            char *st  = json_str(line, "subtype");
            char *res = json_str(line, "result");
            fprintf(stderr, "\n<< ===== result (%s) =====\n   %s\n",
                    st ? st : "?", res ? res : "(no result text)");
            free(st); free(res);
            free(type);
            break;
        }
        else {
            /* terse trace for everything else */
            char *sub = json_str(line, "subtype");
            fprintf(stderr, "<< %s%s%s\n", type,
                    sub ? "/" : "", sub ? sub : "");
            free(sub);
        }
        free(type);
    }

    free(line);
    close(wfd);
    fclose(rf);

    int status = 0;
    waitpid(g_child, &status, 0);
    alarm(0);

    fprintf(stderr, "\n[p1] permission request seen: %s\n",
            perm_seen ? "YES" : "NO (engine self-decided — handshake/mode issue)");
    /* concrete proof: did the Write happen? */
    char path[256];
    snprintf(path, sizeof path, "%s/p1_spike.txt", WORKDIR);
    if (access(path, F_OK) == 0)
        fprintf(stderr, "[p1] %s EXISTS (tool ran)\n", path);
    else
        fprintf(stderr, "[p1] %s absent (tool did not run)\n", path);

    fprintf(stderr, "[p1] child exit status = %d\n",
            WIFEXITED(status) ? WEXITSTATUS(status) : -1);
    return 0;
}
