/* json.h — minimal JSON field scanners for the stream-json protocol.
 * Not a full parser: each scans a flat-ish JSON line for a key and returns the
 * value. Sufficient (and fast) for the engine's newline-delimited frames. */
#ifndef CRUD_JSON_H
#define CRUD_JSON_H

char  *j_str(const char *s, const char *key);          /* "key":"..."  -> malloc'd raw (escapes intact) | NULL */
double j_num(const char *s, const char *key);          /* "key": <num> -> double (0 if absent) */
char  *j_obj(const char *s, const char *key);          /* "key": {...} -> malloc'd raw object | NULL */
char  *j_arr(const char *s, const char *key);          /* "key": [...] -> malloc'd raw array | NULL */
char  *j_escape(const char *src);                      /* plain -> malloc'd JSON-string-escaped */
char  *j_unescape_dup(const char *s);                  /* JSON-string body -> malloc'd decoded utf8 */
const char *j_obj_end(const char *start);              /* `start` at '{' -> ptr just past the matching '}' (string/escape-aware) */

#endif
