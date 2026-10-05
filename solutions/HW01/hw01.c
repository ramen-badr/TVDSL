#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define NSYM 256  /* алфавит: байты 0..255 */
#define MAXS 1024 /* размер массивов состояний НКА и ДКА (с запасом) */
#define TRAP 1    /* номер ловушки в ДКА */

/* ===================== Пункт 1. Регулярные выражения токенов Funny ===================== */

/* Ключевые слова: токен KW_<СЛОВО>, регулярное выражение — само слово. */
static const char *KW[] = {"function", "returns", "requires", "ensures", "uses", "int", "if", "else", "while", "invariant",
                           "assert", "assume", "length", "true", "false", "not", "and", "or", "forall", "exists"};
/* Остальные токены: {имя, регулярное выражение}. */
static const char *RULES[][2] = {
    {"EQ", "=="}, {"NE", "!="}, {"LE", "<="}, {"GE", ">="}, {"FARROW", "=>"},
    {"LT", "<"}, {"GT", ">"}, {"ASSIGN", "="}, {"PLUS", "\\+"}, {"MINUS", "-"}, {"STAR", "\\*"}, {"SLASH", "/"},
    {"LPAREN", "\\("}, {"RPAREN", "\\)"}, {"LBRACKET", "\\["}, {"RBRACKET", "\\]"}, {"LBRACE", "\\{"},
    {"RBRACE", "\\}"}, {"COMMA", ","}, {"SEMI", ";"}, {"COLON", ":"}, {"BAR", "\\|"},
    {"ARROW", "->|→"}, {"INT", "0|[1-9][0-9]*"}, {"BAD_INT", "0[0-9]+"},
    {"IDENT", "[A-Za-z_][A-Za-z0-9_]*"}, {"WS", "[ \t\r\n]+"}, {"COMMENT", "//[^\n]*"}};
#define NKW (int)(sizeof KW / sizeof *KW)
#define NT (NKW + (int)(sizeof RULES / sizeof *RULES))

static char name[NT][20];
static const char *rx[NT];

/* Собирает общий список токенов: сначала ключевые слова, затем остальные токены. */
static void load_tokens(void) {
    for (int i = 0; i < NT; i++) {
        if (i < NKW) {
            int k = sprintf(name[i], "KW_");
            for (const char *q = KW[i]; *q; q++) name[i][k++] = (char)(*q - 32);
            rx[i] = KW[i];
        } else {
            strcpy(name[i], RULES[i - NKW][0]);
            rx[i] = RULES[i - NKW][1];
        }
    }
}

/* ===================== Пункт 2а. Регулярное выражение → НКА (конструкция Томпсона) ===================== */

static int nn, to[MAXS], acc[MAXS], neps[MAXS], eps[MAXS][NT]; /* ε-переходов: у старта NT, у остальных ≤ 2 */
static bool cs[MAXS][NSYM];
static const char *p; /* текущая позиция в разбираемом выражении */

/* Фрагмент НКА: вход s и единственный выход e. */
typedef struct { int s, e; } Frag;

static int new_state(void) { to[nn] = acc[nn] = -1; return nn++; }
static void add_eps(int a, int b) { eps[a][neps[a]++] = b; }
/* Читает один символ выражения с учетом экранирования «\c». */
static int rchar(void) { return (unsigned char)(*p == '\\' ? (p += 2, p[-1]) : *p++); }

static Frag alt(void);

/* Атом: (выражение), символ или класс [...] / [^...]. */
static Frag atom(void) {
    if (*p == '(') { p++; Frag g = alt(); p++; return g; }
    Frag f = {new_state(), new_state()};
    to[f.s] = f.e;
    if (*p != '[') { cs[f.s][rchar()] = true; return f; }
    bool neg = *++p == '^', in[NSYM] = {0};
    if (neg) p++;
    while (*p != ']') {
        int a = rchar(), b = a;
        if (*p == '-' && p[1] != ']') { p++; b = rchar(); }
        while (a <= b) in[a++] = true;
    }
    p++;
    for (int c = 0; c < NSYM; c++) cs[f.s][c] = in[c] != neg;
    return f;
}

/* Постфиксные операции * + ?. */
static Frag rep(void) {
    Frag a = atom();
    while (*p == '*' || *p == '+' || *p == '?') {
        char k = *p++;
        Frag f = {new_state(), new_state()};
        add_eps(f.s, a.s);
        add_eps(a.e, f.e);
        if (k != '+') add_eps(f.s, f.e);
        if (k != '?') add_eps(a.e, a.s);
        a = f;
    }
    return a;
}

/* Конкатенация. */
static Frag cat(void) {
    Frag f = {-1, -1};
    while (*p && *p != '|' && *p != ')') {
        Frag r = rep();
        if (f.s < 0) f = r;
        else { add_eps(f.e, r.s); f.e = r.e; }
    }
    if (f.s < 0) f.s = f.e = new_state();
    return f;
}

/* Альтернатива a|b. */
static Frag alt(void) {
    Frag f = cat();
    while (*p == '|') {
        p++;
        Frag g = cat(), h = {new_state(), new_state()};
        add_eps(h.s, f.s); add_eps(h.s, g.s);
        add_eps(f.e, h.e); add_eps(g.e, h.e);
        f = h;
    }
    return f;
}

/* Построение НКА из регулярного выражения. */
static int build_nfa(void) {
    int start = new_state();
    for (int i = 0; i < NT; i++) {
        p = rx[i];
        Frag f = alt();
        add_eps(start, f.s);
        acc[f.e] = i;
    }
    return start;
}

/* ===================== Пункт 2б. НКА → ДКА ===================== */

typedef uint64_t Set[MAXS / 64];
static Set dset[MAXS];
static int nd, delta[MAXS][NSYM], lab[MAXS];

static bool has(const uint64_t *S, int s) { return S[s / 64] >> (s % 64) & 1; }
static void put(uint64_t *S, int s) { S[s / 64] |= 1ull << (s % 64); }

/* ε-замыкание: дополняет множество S всеми состояниями, достижимыми по ε-переходам. */
static void closure(uint64_t *S) {
    int st[MAXS], sp = 0;
    for (int s = 0; s < nn; s++) if (has(S, s)) st[sp++] = s;
    while (sp) {
        int s = st[--sp];
        for (int i = 0; i < neps[s]; i++)
            if (!has(S, eps[s][i])) { put(S, eps[s][i]); st[sp++] = eps[s][i]; }
    }
}

/* Возвращает номер состояния ДКА для множества S, при необходимости заводит новое. */
static int find_or_add(const uint64_t *S) {
    for (int i = 0; i < nd; i++) if (!memcmp(dset[i], S, sizeof(Set))) return i;
    memcpy(dset[nd], S, sizeof(Set));
    return nd++;
}

static void add_trap(void);

/* Построение ДКА по НКА: старт — состояние 0, ловушка — состояние 1. */
static void nfa_to_dfa(int start) {
    Set S = {0};
    put(S, start);
    closure(S);
    find_or_add(S);
    add_trap();
    for (int d = 0; d < nd; d++) {
        lab[d] = -1;
        for (int s = 0; s < nn; s++)
            if (has(dset[d], s) && acc[s] >= 0 && (lab[d] < 0 || acc[s] < lab[d])) lab[d] = acc[s];
        for (int c = 0; c < NSYM; c++) {
            Set T = {0};
            for (int s = 0; s < nn; s++) if (has(dset[d], s) && to[s] >= 0 && cs[s][c]) put(T, to[s]);
            closure(T);
            delta[d][c] = find_or_add(T);
        }
    }
}

/* ===================== Пункт 2в. Минимизация ДКА (алгоритм Хопкрофта) ===================== */

static int mn, mdelta[MAXS][NSYM], mlab[MAXS], trap;

/* Делим состояния на группы по токену и дробим группы, пока все состояния группы по каждому символу не переходят в одну и ту же группу; группа = состояние минимального ДКА. */
static void minimize_dfa(void) {
    int blk[MAXS], size[MAXS] = {0}, nb = 0, work[MAXS], nw = 0, cnt[MAXS], split[MAXS];
    bool inW[MAXS] = {0}, inA[MAXS], inX[MAXS];
    for (int s = 0; s < nd; s++) {
        int t = 0;
        while (t < s && lab[t] != lab[s]) t++;
        blk[s] = t < s ? blk[t] : nb++;
        size[blk[s]]++;
    }
    for (int b = 0; b < nb; b++) work[nw++] = b, inW[b] = true;
    while (nw) {
        int A = work[--nw];
        inW[A] = false;
        for (int s = 0; s < nd; s++) inA[s] = blk[s] == A;
        for (int c = 0; c < NSYM; c++) {
            memset(cnt, 0, sizeof cnt);
            for (int s = 0; s < nd; s++) if ((inX[s] = inA[delta[s][c]])) cnt[blk[s]]++;
            int n0 = nb;
            for (int b = 0; b < n0; b++) split[b] = cnt[b] && cnt[b] < size[b] ? nb++ : -1;
            for (int s = 0; s < nd; s++)
                if (inX[s] && split[blk[s]] >= 0) { size[blk[s]]--; blk[s] = split[blk[s]]; size[blk[s]]++; }
            for (int b = 0; b < n0; b++) {
                if (split[b] < 0) continue;
                int y = split[b], add = inW[b] || size[y] <= size[b] ? y : b;
                work[nw++] = add, inW[add] = true;
            }
        }
    }
    int id[MAXS], first[MAXS];
    for (int b = 0; b < nb; b++) id[b] = -1;
    for (int s = 0; s < nd; s++) if (id[blk[s]] < 0) first[mn] = s, id[blk[s]] = mn++;
    for (int b = 0; b < mn; b++) {
        mlab[b] = lab[first[b]];
        for (int c = 0; c < NSYM; c++) mdelta[b][c] = id[blk[delta[first[b]][c]]];
    }
    trap = id[blk[TRAP]];
}

/* ===================== Пункт 3. Таблица переходов ===================== */

/* Печатает символ. */
static void putsym(FILE *f, int c) {
    if (c == '\t' || c == '\n' || c == '\r') fprintf(f, "\\%c", c == '\t' ? 't' : c == '\n' ? 'n' : 'r');
    else fprintf(f, c >= 32 && c < 127 && c != '"' && c != '\\' ? "%c" : "\\x%02x", c);
}

/* Записывает в dfa.h таблицу переходов DFA_NEXT[состояние][байт] и метки DFA_ACCEPT. */
static void export_table(void) {
    char sample[MAXS][32] = {{0}};
    bool seen[MAXS] = {[0] = true};
    int queue[MAXS], head = 0, tail = 0;
    for (queue[tail++] = 0; head < tail;) {
        int s = queue[head++];
        for (int c = 0; c < NSYM; c++) {
            int t = mdelta[s][c];
            if (!seen[t] && t != trap) seen[t] = true, snprintf(sample[t], 32, "%s%c", sample[s], c), queue[tail++] = t;
        }
    }
    FILE *f = fopen("dfa.h", "w");
    fprintf(f, "#define DFA_STATES %d\n#define DFA_START 0\n#define DFA_TRAP %d\n\nstatic const char *const DFA_ACCEPT[DFA_STATES] = {\n", mn, trap);
    for (int s = 0; s < mn; s++) {
        if (mlab[s] >= 0) fprintf(f, "    /* %3d */ \"%s\",\n", s, name[mlab[s]]);
        else if (s == trap || s == 0) fprintf(f, "    /* %3d */ 0, /* %s */\n", s, s == trap ? "ловушка DFA_TRAP" : "старт DFA_START");
        else {
            fprintf(f, "    /* %3d */ 0, /* \"", s);
            for (const char *q = sample[s]; *q; q++) putsym(f, (unsigned char)*q);
            fprintf(f, "\" — середина токена, ждем подолжения */\n");
        }
    }
    fprintf(f, "};\n\nstatic const unsigned short DFA_NEXT[DFA_STATES][%d] = {\n", NSYM);
    for (int s = 0; s < mn; s++) {
        fprintf(f, "    /* %d: ", s);
        if (s == trap) fprintf(f, "ловушка");
        else {
            fprintf(f, "\"");
            for (const char *q = sample[s]; *q; q++) putsym(f, (unsigned char)*q);
            fprintf(f, "\"%s%s", mlab[s] < 0 ? "" : " → ", mlab[s] < 0 ? "" : name[mlab[s]]);
        }
        fprintf(f, "; переходы:");
        int k = 0;
        for (int a = 0; a < NSYM; a++) {
            int t = mdelta[s][a], b = a;
            if (t == trap) continue;
            while (b + 1 < NSYM && mdelta[s][b + 1] == t) b++;
            if (b == a + 1) b = a;
            fprintf(f, k++ ? ", '" : " '"), putsym(f, a), fprintf(f, "'");
            if (b > a) fprintf(f, "-'"), putsym(f, b), fprintf(f, "'");
            fprintf(f, " → %d", t);
            a = b;
        }
        fprintf(f, k ? " */\n    {" : " нет, все в ловушку */\n    {");
        for (int c = 0; c < NSYM; c++) fprintf(f, c ? ",%d" : "%d", mdelta[s][c]);
        fprintf(f, "},\n");
    }
    fprintf(f, "};\n");
    fclose(f);
}

/* ===================== Пункт 4. Ловушка ===================== */

/* Ловушка — состояние ДКА для пустого множества НКА: в нее ведут все непокрытые символы. */
static void add_trap(void) {
    Set empty = {0};
    find_or_add(empty);
}

/* ===================== Пункт 5. Тесты: тестовый лексер, тесты токенов, примеры проекта ===================== */

/* Лексер по правилу самого длинного совпадения, на ошибке пишет ERROR@байт. */
static void lex(const char *text, size_t len, char *out) {
    char *o = out;
    *o = 0;
    for (size_t i = 0, end; i < len; i = end) {
        int s = 0, t = -1;
        end = i;
        for (size_t j = i; j < len && s != trap;) {
            s = mdelta[s][(unsigned char)text[j++]];
            if (mlab[s] >= 0) t = mlab[s], end = j;
        }
        const char *sep = o > out ? " " : "";
        if (t < 0 || !strcmp(name[t], "BAD_INT")) { sprintf(o, "%sERROR@%zu", sep, i); return; }
        if (!strcmp(name[t], "WS") || !strcmp(name[t], "COMMENT")) continue;
        o += sprintf(o, "%s%s", sep, name[t]);
        if (!strcmp(name[t], "IDENT") || !strcmp(name[t], "INT")) o += sprintf(o, "(%.*s)", (int)(end - i), text + i);
    }
}

/* Тесты {вход, ожидаемые токены}; ERROR@i — ошибка на i-том байте. */
static const char *TESTS[][2] = {
    {"", ""},
    {" ", ""},
    {"\t\t", ""},
    {"\r\n", ""},
    {" \t\r\n \r\n\t ", ""},
    {"a \t\r\n b", "IDENT(a) IDENT(b)"},
    {"0", "INT(0)"},
    {"00", "ERROR@0"},
    {"01", "ERROR@0"},
    {"007", "ERROR@0"},
    {"10", "INT(10)"},
    {"1234567890", "INT(1234567890)"},
    {"0 0", "INT(0) INT(0)"},
    {"x 01", "IDENT(x) ERROR@2"},
    {"-0", "MINUS INT(0)"},
    {"0x", "INT(0) IDENT(x)"},
    {"_", "IDENT(_)"},
    {"_a1", "IDENT(_a1)"},
    {"a_b", "IDENT(a_b)"},
    {"__x__", "IDENT(__x__)"},
    {"A9z", "IDENT(A9z)"},
    {"x1_", "IDENT(x1_)"},
    {"function", "KW_FUNCTION"},
    {"returns", "KW_RETURNS"},
    {"requires", "KW_REQUIRES"},
    {"ensures", "KW_ENSURES"},
    {"uses", "KW_USES"},
    {"int", "KW_INT"},
    {"while", "KW_WHILE"},
    {"if", "KW_IF"},
    {"else", "KW_ELSE"},
    {"assert", "KW_ASSERT"},
    {"assume", "KW_ASSUME"},
    {"invariant", "KW_INVARIANT"},
    {"length", "KW_LENGTH"},
    {"true", "KW_TRUE"},
    {"false", "KW_FALSE"},
    {"not", "KW_NOT"},
    {"and", "KW_AND"},
    {"or", "KW_OR"},
    {"forall", "KW_FORALL"},
    {"exists", "KW_EXISTS"},
    {"functions", "IDENT(functions)"},
    {"returns_", "IDENT(returns_)"},
    {"iff", "IDENT(iff)"},
    {"If", "IDENT(If)"},
    {"whil", "IDENT(whil)"},
    {"or1", "IDENT(or1)"},
    {"_if", "IDENT(_if)"},
    {"int[]", "KW_INT LBRACKET RBRACKET"},
    {"if(", "KW_IF LPAREN"},
    {"()[]{},;", "LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE COMMA SEMI"},
    {"+ - * / == != <= >= < > =", "PLUS MINUS STAR SLASH EQ NE LE GE LT GT ASSIGN"},
    {": | -> =>", "COLON BAR ARROW FARROW"},
    {"a \xe2\x86\x92 b", "IDENT(a) ARROW IDENT(b)"},
    {"\xe2\x86", "ERROR@0"},
    {"<=<>=>", "LE LT GE GT"},
    {"===", "EQ ASSIGN"},
    {"!==", "NE ASSIGN"},
    {"-->", "MINUS ARROW"},
    {"a-1", "IDENT(a) MINUS INT(1)"},
    {"!", "ERROR@0"},
    {"a ! b", "IDENT(a) ERROR@2"},
    {"//", ""},
    {"// hello", ""},
    {"//x\n", ""},
    {"x // c == 1\ny", "IDENT(x) IDENT(y)"},
    {"x//c\r\ny", "IDENT(x) IDENT(y)"},
    {"a/b", "IDENT(a) SLASH IDENT(b)"},
    {"/ /", "SLASH SLASH"},
    {"/// triple", ""},
    {"\xc3\xa9", "ERROR@0"},
    {"x=\xc3\xa9", "IDENT(x) ASSIGN ERROR@2"},
    {"\xd0\xb6\xd0\xb8", "ERROR@0"},
    {"// \xd0\xbf\xd1\x80\xd0\xb8\xd0\xb2\xd0\xb5\xd1\x82", ""},
    {"x // \xc3\xa9\ny\xc3\xa9", "IDENT(x) IDENT(y) ERROR@9"},
    {"\x01", "ERROR@0"},
    {"\x7f", "ERROR@0"},
    {"@", "ERROR@0"},
    {"#", "ERROR@0"},
    {"$", "ERROR@0"},
    {"\"s\"", "ERROR@0"},
    {"'", "ERROR@0"},
    {"\\", "ERROR@0"},
    {"foo @ 42", "IDENT(foo) ERROR@4"},
    {"main() returns r:int {\n    r = 1 + 2 * 3;\n}\n", "IDENT(main) LPAREN RPAREN KW_RETURNS IDENT(r) COLON KW_INT LBRACE IDENT(r) ASSIGN INT(1) PLUS INT(2) STAR INT(3) SEMI RBRACE"},
    {"f(a: int[]) requires length(a) > 0 returns s: int uses i { while (i < length(a)) invariant forall(k: int | k >= 0) -> true { a[i] = s / 2; } }", "IDENT(f) LPAREN IDENT(a) COLON KW_INT LBRACKET RBRACKET RPAREN KW_REQUIRES KW_LENGTH LPAREN IDENT(a) RPAREN GT INT(0) KW_RETURNS IDENT(s) COLON KW_INT KW_USES IDENT(i) LBRACE KW_WHILE LPAREN IDENT(i) LT KW_LENGTH LPAREN IDENT(a) RPAREN RPAREN KW_INVARIANT KW_FORALL LPAREN IDENT(k) COLON KW_INT BAR IDENT(k) GE INT(0) RPAREN ARROW KW_TRUE LBRACE IDENT(a) LBRACKET IDENT(i) RBRACKET ASSIGN IDENT(s) SLASH INT(2) SEMI RBRACE RBRACE"},
};

/* Прогоняет TESTS через лексер, печатает статус каждого теста. Возвращает число проваленных. */
static int test_tokens(void) {
    int n = sizeof TESTS / sizeof *TESTS, failed = 0;
    char got[16384];
    for (int i = 0; i < n; i++) {
        lex(TESTS[i][0], strlen(TESTS[i][0]), got);
        bool ok = !strcmp(got, TESTS[i][1]);
        failed += !ok;
        printf("[%s] \"", ok ? "PASS" : "FAIL");
        for (const char *q = TESTS[i][0]; *q; q++) putsym(stdout, (unsigned char)*q);
        printf("\" -> %s", got);
        printf(ok ? "\n" : "   (ожидалось: %s)\n", TESTS[i][1]);
    }
    printf("Пройдено тестов: %d/%d\n", n - failed, n);
    return failed;
}

/* Разбивает файлы на токены; файл проходит, если в нем нет лексических ошибок. Возвращает число ошибочных. */
static int test_examples(int n, char **paths) {
    static char text[1 << 20], out[1 << 22];
    int failed = 0;
    for (int i = 0; i < n; i++) {
        FILE *f = fopen(paths[i], "rb");
        if (!f) { perror(paths[i]); failed++; continue; }
        size_t len = fread(text, 1, sizeof text, f);
        fclose(f);
        lex(text, len, out);
        bool ok = !strstr(out, "ERROR@");
        failed += !ok;
        printf("[%s] %s: %s\n", ok ? "PASS" : "FAIL", paths[i], out);
    }
    if (n) printf("Файлов без лексических ошибок: %d/%d\n", n - failed, n);
    return failed;
}

/* Выполняет пункты задания по порядку и печатает отчет по каждому. */
int main(int argc, char **argv) {
    load_tokens();
    printf("Пункт 1. Количество регулярных выражений токенов: %d\n", NT);
    int start = build_nfa();
    printf("Пункт 2а. НКА построен: %d состояний\n", nn);
    nfa_to_dfa(start);
    printf("Пункт 2б. ДКА построен: %d состояний\n", nd);
    minimize_dfa();
    printf("Пункт 2в. ДКА минимизирован: %d состояний\n", mn);
    export_table();
    printf("Пункт 3. Таблица переходов минимального ДКА сохранена в dfa.h\n");
    printf("Пункт 4. Ловушка создана под состоянием %d.\n", trap);
    printf("Пункт 5. Тесты\n");
    int failed = test_tokens();
    printf("\n");
    failed += test_examples(argc - 1, argv + 1);
    return failed ? 1 : 0;
}
