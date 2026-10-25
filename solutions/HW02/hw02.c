#include <setjmp.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dfa.h"

#define MAXTOK 65536 /* размер массива токенов */
#define MAXERR 20 /* количество ошибок для остановки */

static FILE *out; // файл для записи

/* Коды токенов (ключевые слова KW, затем правила RULES). */
enum { T_FUNCTION, T_RETURNS, T_REQUIRES, T_ENSURES, T_USES, T_INT, T_IF, T_ELSE, T_WHILE,
       T_INVARIANT, T_ASSERT, T_ASSUME, T_LENGTH, T_TRUE, T_FALSE, T_NOT, T_AND, T_OR, T_FORALL,
       T_EXISTS,T_EQ, T_NE, T_LE, T_GE, T_FARROW, T_LT, T_GT, T_ASSIGN, T_PLUS, T_MINUS,
       T_STAR, T_SLASH, T_LPAREN, T_RPAREN, T_LBRACKET, T_RBRACKET, T_LBRACE, T_RBRACE, T_COMMA,
       T_SEMI, T_COLON, T_BAR, T_ARROW, T_INT_LIT, T_BADINT, T_IDENT, T_WS, T_COMMENT, T_EOF };

/* Токен: код, позиция и лексема. */
typedef struct { int code, line, col; const char *lex; size_t len; } Tok;
static Tok toks[MAXTOK];
static int ntok, toki;

/* Виды узлов AST; дамп печатает имя вида, имя/операцию и детей с отступом. */
enum { N_MODULE, N_FUNC, N_FORMULA, N_PARAM, N_LOCAL, N_REQUIRES, N_RETURNS, N_ENSURES, N_USES, N_BLOCK,
       N_ASSIGN, N_UPDATE, N_MASSIGN, N_VARS, N_IF, N_ELSE, N_WHILE, N_INVARIANT, N_ASSERT, N_ASSUME,
       N_INT, N_VAR, N_CALL, N_INDEX, N_NEG, N_BIN, N_NOT, N_TRUE, N_FALSE, N_FORALL, N_EXISTS };

/* Узел: вид, позиция, имя/операция, значение числа, список детей; хвост. */
typedef struct Node {
    int kind, line, col, num;
    const char *str;
    struct Node *kid, *next, **tail;
} Node;

static int nerr;             /* число синтаксических ошибок */
static bool giveup;          /* флаг остановки разбора при большом количестве ошибок */
static jmp_buf rec[256];     /* стек точек восстановления */
static int nrec;

/* ===================== Пункт 1-2. Грамматика LL(1): рекурсивный спуск ===================== */

static Node *node(int kind);
static const char *lexstr(const Tok *t);
static void add(Node *p, Node *c);
static void synerr_txt(const char *want) __attribute__((noreturn));
static bool check(int c), eat(int c);
static void expect(int c);
static void panic_stmt(void), panic_decl(void);
static const char *got_desc(void);

static Node *parse_expr(void), *parse_stmt(void), *parse_or(void), *parse_and(void), *parse_not(void),
            *parse_cmp(void), *parse_arith(void), *parse_term(void), *parse_unary(void), *parse_primary(void);

/* Тип: int или int[]; возвращает true для массива. */
static bool parse_type(void) {
    expect(T_INT);
    if (eat(T_LBRACKET)) { expect(T_RBRACKET); return true; }
    return false;
}

/* Определение переменной «имя: тип». */
static Node *parse_vardef(void) {
    Node *v = node(N_PARAM);
    v->str = lexstr(&toks[toki]);
    expect(T_IDENT);
    expect(T_COLON);
    v->num = parse_type();
    return v;
}

/* Локальная переменная «имя [: тип]»; num: 0 — без типа, 1 — int, 2 — int[]. */
static Node *parse_local(void) {
    Node *v = node(N_LOCAL);
    v->str = lexstr(&toks[toki]);
    expect(T_IDENT);
    if (eat(T_COLON)) v->num = 1 + parse_type();
    return v;
}

/* Вызов: имя '(' [аргументы] ')' — правая часть кортежного присваивания. */
static Node *parse_call(void) {
    Node *c = node(N_CALL);
    c->str = lexstr(&toks[toki]);
    expect(T_IDENT);
    expect(T_LPAREN);
    if (!check(T_RPAREN)) do add(c, parse_expr()); while (eat(T_COMMA));
    expect(T_RPAREN);
    return c;
}

/* Блок: '{' { оператор } '}'; при ошибке — паника до ';'/'}' и разбор продолжается. */
static Node *parse_block(void) {
    Node *b = node(N_BLOCK);
    expect(T_LBRACE);
    while (!check(T_RBRACE) && !check(T_EOF) && !giveup) {
        if (nrec >= (int)(sizeof rec / sizeof *rec)) { giveup = true; break; }
        int d = nrec++;
        if (setjmp(rec[d]) == 0) { add(b, parse_stmt()); nrec = d; }
        else { nrec = d; panic_stmt(); }
    }
    expect(T_RBRACE);
    return b;
}

/* Условный оператор; else связывается с ближайшим if. */
static Node *parse_if(void) {
    Node *n = node(N_IF);
    expect(T_IF);
    expect(T_LPAREN);
    add(n, parse_expr());
    expect(T_RPAREN);
    add(n, parse_stmt());
    if (eat(T_ELSE)) { Node *e = node(N_ELSE); add(n, e); add(e, parse_stmt()); }
    return n;
}

/* Цикл с необязательным инвариантом (если опущен — считается true). */
static Node *parse_while(void) {
    Node *n = node(N_WHILE);
    expect(T_WHILE);
    expect(T_LPAREN);
    add(n, parse_expr());
    expect(T_RPAREN);
    if (eat(T_INVARIANT)) { Node *i = node(N_INVARIANT); add(n, i); add(i, parse_expr()); }
    add(n, parse_stmt());
    return n;
}

/* Присваивание: a[i] = v | r = выражение | p, q = вызов. */
static Node *parse_assign(void) {
    Node *lhs = node(N_VAR), *a = node(N_ASSIGN);
    lhs->str = lexstr(&toks[toki]);
    expect(T_IDENT);
    if (eat(T_LBRACKET)) {
        a->kind = N_UPDATE;
        add(a, lhs);
        add(a, parse_expr());
        expect(T_RBRACKET);
        expect(T_ASSIGN);
    } else if (eat(T_COMMA)) {
        Node *vs = node(N_VARS);
        a->kind = N_MASSIGN;
        add(vs, lhs);
        do {
            Node *v = node(N_VAR);
            v->str = lexstr(&toks[toki]);
            expect(T_IDENT);
            add(vs, v);
        } while (eat(T_COMMA));
        add(a, vs);
        expect(T_ASSIGN);
        add(a, parse_call());
        expect(T_SEMI);
        return a;
    } else {
        add(a, lhs);
        expect(T_ASSIGN);
    }
    add(a, parse_expr());
    expect(T_SEMI);
    return a;
}

/* Оператор по первому токену (все альтернативы начинаются с разных токенов — LL(1)). */
static Node *parse_stmt(void) {
    switch (toks[toki].code) {
    case T_LBRACE: return parse_block();
    case T_IF:     return parse_if();
    case T_WHILE:  return parse_while();
    case T_ASSERT: case T_ASSUME: {
        Node *n = node(toks[toki].code == T_ASSERT ? N_ASSERT : N_ASSUME);
        toki++;
        add(n, parse_expr());
        expect(T_SEMI);
        return n;
    }
    case T_IDENT:  return parse_assign();
    default:       synerr_txt("оператор");
    }
}

/* Объявление: [function] имя(параметры) и далее формула («=>») или функция («returns»). */
static Node *parse_decl(void) {
    Node *d = node(N_FORMULA);
    eat(T_FUNCTION);
    d->str = lexstr(&toks[toki]);
    expect(T_IDENT);
    expect(T_LPAREN);
    if (!check(T_RPAREN)) do add(d, parse_vardef()); while (eat(T_COMMA));
    expect(T_RPAREN);
    if (eat(T_FARROW)) {
        add(d, parse_expr());
        expect(T_SEMI);
        return d;
    }
    d->kind = N_FUNC;
    if (eat(T_REQUIRES)) { Node *r = node(N_REQUIRES); add(d, r); add(r, parse_expr()); }
    expect(T_RETURNS);
    Node *rets = node(N_RETURNS);
    add(d, rets);
    add(rets, parse_vardef());
    while (eat(T_COMMA)) add(rets, parse_vardef());
    if (eat(T_ENSURES)) { Node *e = node(N_ENSURES); add(d, e); add(e, parse_expr()); }
    if (eat(T_USES)) {
        Node *u = node(N_USES);
        add(d, u);
        do add(u, parse_local()); while (eat(T_COMMA));
    }
    add(d, parse_stmt());
    return d;
}

/* Модуль: { объявление }; при ошибке — паника до следующего объявления. */
static Node *parse_module(void) {
    Node *m = node(N_MODULE);
    while (!check(T_EOF) && !giveup) {
        if (nrec >= (int)(sizeof rec / sizeof *rec)) { giveup = true; break; }
        int d = nrec++;
        if (setjmp(rec[d]) == 0) { add(m, parse_decl()); nrec = d; }
        else { nrec = d; panic_decl(); }
    }
    return m;
}

/* Знак сравнения для узла N_BIN. */
static const char *opstr(int c) {
    switch (c) {
    case T_EQ: return "=="; case T_NE: return "!="; case T_LE: return "<=";
    case T_GE: return ">="; case T_LT: return "<";  default:  return ">";
    }
}

/* Импликация. */
static Node *parse_expr(void) {
    Node *n = parse_or();
    if (eat(T_ARROW)) {
        Node *b = node(N_BIN);
        b->str = "->";
        add(b, n);
        add(b, parse_expr());
        return b;
    }
    return n;
}

/* or. */
static Node *parse_or(void) {
    Node *n = parse_and();
    while (eat(T_OR)) {
        Node *b = node(N_BIN);
        b->str = "or";
        add(b, n);
        add(b, parse_and());
        n = b;
    }
    return n;
}

/* and. */
static Node *parse_and(void) {
    Node *n = parse_not();
    while (eat(T_AND)) {
        Node *b = node(N_BIN);
        b->str = "and";
        add(b, n);
        add(b, parse_not());
        n = b;
    }
    return n;
}

/* not. */
static Node *parse_not(void) {
    if (eat(T_NOT)) {
        Node *n = node(N_NOT);
        add(n, parse_not());
        return n;
    }
    return parse_cmp();
}

/* Одно сравнение. */
static Node *parse_cmp(void) {
    Node *n = parse_arith();
    int c = toks[toki].code;
    if (c == T_EQ || c == T_NE || c == T_LE || c == T_GE || c == T_LT || c == T_GT) {
        Node *b = node(N_BIN);
        b->str = opstr(c);
        toki++;
        add(b, n);
        add(b, parse_arith());
        return b;
    }
    return n;
}

/* Сложение и вычитание. */
static Node *parse_arith(void) {
    Node *n = parse_term();
    while (check(T_PLUS) || check(T_MINUS)) {
        Node *b = node(N_BIN);
        b->str = toks[toki++].code == T_PLUS ? "+" : "-";
        add(b, n);
        add(b, parse_term());
        n = b;
    }
    return n;
}

/* Умножение и деление. */
static Node *parse_term(void) {
    Node *n = parse_unary();
    while (check(T_STAR) || check(T_SLASH)) {
        Node *b = node(N_BIN);
        b->str = toks[toki++].code == T_STAR ? "*" : "/";
        add(b, n);
        add(b, parse_unary());
        n = b;
    }
    return n;
}

/* Унарный минус. */
static Node *parse_unary(void) {
    if (eat(T_MINUS)) {
        Node *n = node(N_NEG);
        add(n, parse_unary());
        return n;
    }
    return parse_primary();
}

/* Первичное: число, true/false, квантор, имя с вызовом/индексом, скобка. */
static Node *parse_primary(void) {
    switch (toks[toki].code) {
    case T_INT_LIT: {
        Node *n = node(N_INT);
        n->num = atoi(lexstr(&toks[toki]));
        toki++;
        return n;
    }
    case T_TRUE: case T_FALSE:
        return node(toks[toki++].code == T_TRUE ? N_TRUE : N_FALSE);
    case T_FORALL: case T_EXISTS: {
        Node *q = node(toks[toki].code == T_FORALL ? N_FORALL : N_EXISTS);
        toki++;
        expect(T_LPAREN);
        add(q, parse_vardef());
        expect(T_BAR);
        add(q, parse_expr());
        expect(T_RPAREN);
        return q;
    }
    case T_IDENT: case T_LENGTH: {
        Node *n = node(N_VAR);
        n->str = lexstr(&toks[toki]);
        toki++;
        if (eat(T_LPAREN)) {
            n->kind = N_CALL;
            if (!check(T_RPAREN)) do add(n, parse_expr()); while (eat(T_COMMA));
            expect(T_RPAREN);
        }
        while (eat(T_LBRACKET)) {
            Node *ix = node(N_INDEX);
            add(ix, n);
            add(ix, parse_expr());
            expect(T_RBRACKET);
            n = ix;
        }
        return n;
    }
    case T_LPAREN: {
        toki++;
        Node *n = parse_expr();
        expect(T_RPAREN);
        return n;
    }
    default:
        synerr_txt("выражение");
    }
}

/* ===================== Пункт 3. Лексер ===================== */

/* Имена токенов. */
static const char *const TNAME[] = { "KW_FUNCTION", "KW_RETURNS", "KW_REQUIRES", "KW_ENSURES",
    "KW_USES", "KW_INT", "KW_IF", "KW_ELSE", "KW_WHILE", "KW_INVARIANT", "KW_ASSERT", "KW_ASSUME",
    "KW_LENGTH", "KW_TRUE", "KW_FALSE", "KW_NOT", "KW_AND", "KW_OR", "KW_FORALL", "KW_EXISTS",
    "EQ", "NE", "LE", "GE", "FARROW", "LT", "GT", "ASSIGN", "PLUS", "MINUS", "STAR", "SLASH",
    "LPAREN", "RPAREN", "LBRACKET", "RBRACKET", "LBRACE", "RBRACE", "COMMA", "SEMI", "COLON",
    "BAR", "ARROW", "INT", "BAD_INT", "IDENT", "WS", "COMMENT" };

/* Код токена по имени. */
static int code_of(const char *s) {
    for (int c = 0; c < T_EOF; c++)
        if (!strcmp(TNAME[c], s)) return c;
    return -1;
}

/* Лексер: самое длинное совпадение по ДКА. Возвращает 0 при успехе, 1 при лексической ошибке. */
static int lex_all(const char *s, size_t n) {
    size_t i = 0;
    int line = 1, col = 1;
    while (i < n) {
        int st = DFA_START, acc = -1, tline = line, tcol = col;
        size_t j = i, end = i;
        while (j < n) {
            st = DFA_NEXT[st][(unsigned char)s[j++]];
            if (st == DFA_TRAP) break;
            if (DFA_ACCEPT[st]) { acc = code_of(DFA_ACCEPT[st]); end = j; }
        }
        if (end == i || acc == T_BADINT) {
            fprintf(out, "%d:%d: лексическая ошибка: %s\n", tline, tcol,
                    end == i ? "нераспознанный символ" : "число с ведущим нулем");
            return 1;
        }
        for (size_t k = i; k < end; k++) col = s[k] == '\n' ? (line++, 1) : col + 1;
        if (acc != T_WS && acc != T_COMMENT) {
            if (ntok >= MAXTOK - 1) {
                fprintf(out, "%d:%d: лексическая ошибка: файл слишком велик\n", tline, tcol);
                return 1;
            }
            toks[ntok++] = (Tok){acc, tline, tcol, s + i, end - i};
        }
        i = end;
    }
    toks[ntok] = (Tok){T_EOF, line, col, s + n, 0};
    return 0;
}

/* ===================== Пункт 4. AST: пул узлов, вывод и полный разбор ===================== */

static const char *const NNAME[] = { "module", "function", "formula", "param", "local",
    "requires", "returns", "ensures", "uses", "block", "assign", "update", "massign", "vars",
    "if", "else", "while", "invariant", "assert", "assume", "int", "var", "call", "index",
    "neg", "bin", "not", "true", "false", "forall", "exists" };

static Node pool[1 << 16];
static int npool;
static char spool[1 << 20];
static size_t sp;

/* Новый узел; позиция берется у текущего токена. */
static Node *node(int kind) {
    if (npool >= (int)(sizeof pool / sizeof *pool) || sp + 256 > sizeof spool) {
        fprintf(out, "программа слишком велика\n");
        exit(1);
    }
    Node *n = &pool[npool++];
    *n = (Node){0};
    n->kind = kind;
    n->line = toks[toki].line;
    n->col = toks[toki].col;
    n->tail = &n->kid;
    return n;
}

/* Копирует лексему токена в пул строк. */
static const char *lexstr(const Tok *t) {
    char *s = spool + sp;
    memcpy(s, t->lex, t->len);
    s[t->len] = 0;
    sp += t->len + 1;
    return s;
}

/* Добавляет ребенка в конец списка детей узла. */
static void add(Node *p, Node *c) { *p->tail = c, p->tail = &c->next; }

/* Печать одного узла с детьми. */
static void pnode(FILE *f, const Node *n, int d) {
    fprintf(f, "(%s", n->kind == N_BIN ? n->str : NNAME[n->kind]);
    if (n->kind != N_BIN && n->str) fprintf(f, " %s", n->str);
    if (n->kind == N_INT) fprintf(f, " %d", n->num);
    if (n->kind == N_PARAM) fprintf(f, " int%s", n->num ? "[]" : "");
    if (n->kind == N_LOCAL && n->num) fprintf(f, " int%s", n->num == 2 ? "[]" : "");
    for (const Node *c = n->kid; c; c = c->next) {
        if (c->kid) fprintf(f, "\n%*s", 2 * (d + 1), "");
        else fprintf(f, " ");
        pnode(f, c, d + 1);
    }
    fprintf(f, ")");
}

/* Печать AST: узлы списка, каждый с новой строки и отступом d. */
static void dump(FILE *f, const Node *n, int d) {
    for (; n; n = n->next) {
        fprintf(f, "%*s", 2 * d, "");
        pnode(f, n, d);
        fprintf(f, "\n");
    }
}

/* Полный разбор: лексер + парсер; печатает ошибки или AST в out. Возвращает число ошибок. */
static int parse_program(const char *src, size_t len) {
    ntok = toki = nerr = 0;
    npool = 0;
    sp = 0;
    nrec = 0;
    giveup = false;
    if (lex_all(src, len)) return 1;
    Node *m = parse_module();
    if (!m->kid && !nerr) {
        fprintf(out, "%d:%d: ожидалось объявление функции или формулы, получено %s\n",
                toks[toki].line, toks[toki].col, got_desc());
        nerr++;
    }
    if (!nerr) dump(out, m->kid, 0);
    return nerr;
}

/* ===================== Пункт 5. Ошибки: позиция в сообщении и режим паники ===================== */

/* Человекочитаемые имена токенов для сообщений об ошибках. */
static const char *const HUMAN[] = { "'function'", "'returns'", "'requires'", "'ensures'",
    "'uses'", "'int'", "'if'", "'else'", "'while'", "'invariant'", "'assert'", "'assume'",
    "'length'", "'true'", "'false'", "'not'", "'and'", "'or'", "'forall'", "'exists'",
    "'=='", "'!='", "'<='", "'>='", "'=>'", "'<'", "'>'", "'='", "'+'", "'-'", "'*'", "'/'",
    "'('", "')'", "'['", "']'", "'{'", "'}'", "','", "';'", "':'", "'|'", "'->'",
    "число", "число с ведущим нулем", "имя", "пробел", "комментарий", "конец файла" };

/* Текст текущего токена для сообщения: имя и число — с лексемой. */
static const char *got_desc(void) {
    static char g[80];
    const Tok *t = &toks[toki];
    if (t->code == T_IDENT || t->code == T_INT_LIT)
        snprintf(g, sizeof g, "%s '%.*s'", HUMAN[t->code], (int)t->len, t->lex);
    else snprintf(g, sizeof g, "%s", HUMAN[t->code]);
    return g;
}

/* Сообщает синтаксическую ошибку с позицией и уходит на ближайшую точку восстановления. */
static void synerr_txt(const char *want) {
    if (++nerr > MAXERR) {
        if (!giveup) fprintf(out, "слишком много ошибок: разбор остановлен\n");
        giveup = true;
    } else
        fprintf(out, "%d:%d: ожидалось %s, получено %s\n", toks[toki].line, toks[toki].col,
                want, got_desc());
    longjmp(rec[nrec - 1], 1);
}

static bool check(int c) { return toks[toki].code == c; }
static bool eat(int c) { if (check(c)) return toki++, true; return false; }
static void expect(int c) { if (!eat(c)) synerr_txt(HUMAN[c]); }

/* Паника на уровне оператора: пропуск до ';' (поглощается), '}' или конца файла. */
static void panic_stmt(void) {
    while (!check(T_SEMI) && !check(T_RBRACE) && !check(T_EOF)) toki++;
    eat(T_SEMI);
}

/* Паника на уровне модуля: пропуск до ';' (поглощается), начала объявления или конца файла. */
static void panic_decl(void) {
    while (!check(T_SEMI) && !check(T_IDENT) && !check(T_EOF)) toki++;
    eat(T_SEMI);
}

/* ===================== Пункт 6. Тесты: встроенные и файлы проекта ===================== */

/* Тесты {имя, вход, ожидание}: ожидание — точный дамп AST (позитивные) или первая строка диагностики (негативные). */
static const struct { const char *name, *src, *want; } TESTS[] = {
    {"присваивание и приоритет * над +", "main() returns r:int { r = 1 + 2 * 3; }",
     "(function main\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assign (var r)\n"
     "      (+ (int 1)\n"
     "        (* (int 2) (int 3))))))\n"},
    {"параметры, вызов, унарный минус", "add(a:int, b:int) returns r:int { r = add(a, b) + -1; }",
     "(function add (param a int) (param b int)\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assign (var r)\n"
     "      (+\n"
     "        (call add (var a) (var b))\n"
     "        (neg (int 1))))))\n"},
    {"кортежное присваивание", "split(x:int) returns a:int, b:int { p, q = split(9); }",
     "(function split (param x int)\n"
     "  (returns (param a int) (param b int))\n"
     "  (block\n"
     "    (massign\n"
     "      (vars (var p) (var q))\n"
     "      (call split (int 9)))))\n"},
    {"dangling else — к ближайшему if",
     "f(x:int) returns r:int { if (x > 0) if (x > 1) r = 1; else r = 2; else r = 3; }",
     "(function f (param x int)\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (if\n"
     "      (> (var x) (int 0))\n"
     "      (if\n"
     "        (> (var x) (int 1))\n"
     "        (assign (var r) (int 1))\n"
     "        (else\n"
     "          (assign (var r) (int 2))))\n"
     "      (else\n"
     "        (assign (var r) (int 3))))))\n"},
    {"while с инвариантом",
     "sum(n:int) returns r:int { while (i < n) invariant 0 <= i and i <= n { i = i + 1; } }",
     "(function sum (param n int)\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (while\n"
     "      (< (var i) (var n))\n"
     "      (invariant\n"
     "        (and\n"
     "          (<= (int 0) (var i))\n"
     "          (<= (var i) (var n))))\n"
     "      (block\n"
     "        (assign (var i)\n"
     "          (+ (var i) (int 1)))))))\n"},
    {"assume и assert", "f(x:int, y:int) returns r:int { assume y != 0; r = x / y; assert r * y == x; }",
     "(function f (param x int) (param y int)\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assume\n"
     "      (!= (var y) (int 0)))\n"
     "    (assign (var r)\n"
     "      (/ (var x) (var y)))\n"
     "    (assert\n"
     "      (==\n"
     "        (* (var r) (var y)) (var x)))))\n"},
    {"массивы: копия, update-сахар, a[a[1]], length",
     "f(a:int[]) returns b:int[] { b = a; b[0] = a[a[1]] + length(b); }",
     "(function f (param a int[])\n"
     "  (returns (param b int[]))\n"
     "  (block\n"
     "    (assign (var b) (var a))\n"
     "    (update (var b) (int 0)\n"
     "      (+\n"
     "        (index (var a)\n"
     "          (index (var a) (int 1)))\n"
     "        (call length (var b))))))\n"},
    {"формула с forall и импликацией",
     "is_sorted(a:int[], l:int, r:int) => forall (k:int | l <= k and k + 1 <= r -> a[k] <= a[k + 1]);",
     "(formula is_sorted (param a int[]) (param l int) (param r int)\n"
     "  (forall (param k int)\n"
     "    (->\n"
     "      (and\n"
     "        (<= (var l) (var k))\n"
     "        (<=\n"
     "          (+ (var k) (int 1)) (var r)))\n"
     "      (<=\n"
     "        (index (var a) (var k))\n"
     "        (index (var a)\n"
     "          (+ (var k) (int 1)))))))\n"},
    {"requires/ensures/uses",
     "f(x:int) requires x >= 0 returns y:int, z:int ensures y > x uses i, j:int[] { y = x + 1; }",
     "(function f (param x int)\n"
     "  (requires\n"
     "    (>= (var x) (int 0)))\n"
     "  (returns (param y int) (param z int))\n"
     "  (ensures\n"
     "    (> (var y) (var x)))\n"
     "  (uses (local i) (local j int[]))\n"
     "  (block\n"
     "    (assign (var y)\n"
     "      (+ (var x) (int 1)))))\n"},
    {"приоритеты: not выше сравнения, -> ниже or",
     "f() returns r:int { assert not 1 < 2 and 3 > 4 or true -> false; }",
     "(function f\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assert\n"
     "      (->\n"
     "        (or\n"
     "          (and\n"
     "            (not\n"
     "              (< (int 1) (int 2)))\n"
     "            (> (int 3) (int 4))) (true)) (false)))))\n"},
    {"CRLF и комментарии", "main() returns r:int {\r\n // c\r\n r = 1;\r\n}\r\n",
     "(function main\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assign (var r) (int 1))))\n"},
    {"вложенные блоки", "f() returns r:int { { r = 1; { r = 2; } } }",
     "(function f\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (block\n"
     "      (assign (var r) (int 1))\n"
     "      (block\n"
     "        (assign (var r) (int 2))))))\n"},
    {"квантор exists",
     "f(a:int[]) returns r:int { assert exists (i:int | 0 <= i and i < length(a)) -> a[i] > 0; }",
     "(function f (param a int[])\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assert\n"
     "      (->\n"
     "        (exists (param i int)\n"
     "          (and\n"
     "            (<= (int 0) (var i))\n"
     "            (< (var i)\n"
     "              (call length (var a)))))\n"
     "        (>\n"
     "          (index (var a) (var i)) (int 0))))))\n"},
    {"ключевое слово function", "function f(x:int) returns r:int { r = x; }",
     "(function f (param x int)\n"
     "  (returns (param r int))\n"
     "  (block\n"
     "    (assign (var r) (var x))))\n"},
    {"пустой ввод", "", "1:1: ожидалось объявление функции или формулы, получено конец файла"},
    {"пропущена ';'", "main() returns r:int {\n r = 1 + 2\n}\n",
     "3:1: ожидалось ';', получено '}'"},
    {"пропущена ')'", "main() returns r:int {\n if (r > 0 {\n r = 1;\n }\n}\n",
     "2:12: ожидалось ')', получено '{'"},
    {"неверный оператор '=='", "main() returns r:int { r == 1; }",
     "1:26: ожидалось '=', получено '=='"},
    {"лишний токен после модуля", "main() returns r:int { r = 1; } }",
     "1:33: ожидалось имя, получено '}'"},
    {"незакрытый блок", "main() returns r:int { r = 1;",
     "1:30: ожидалось '}', получено конец файла"},
    {"кортеж без вызова", "main() returns r:int { p, q = 1 + 2; }",
     "1:31: ожидалось имя, получено число '1'"},
    {"ключевое слово как имя функции", "int() returns r:int { r = 1; }",
     "1:1: ожидалось имя, получено 'int'"},
    {"число с ведущим нулем", "main() returns r:int { r = 01; }",
     "1:28: лексическая ошибка: число с ведущим нулем"},
};

/* Прогон одного теста. */
static int run_case(const char *src, const char *want, char *got, size_t cap) {
    static char tbuf[1 << 16];
    FILE *f = fmemopen(tbuf, sizeof tbuf, "w"), *saved = out;
    out = f;
    int n = parse_program(src, strlen(src));
    out = saved;
    fclose(f);
    if (n) {
        char *eol = strchr(tbuf, '\n');
        if (eol) *eol = 0;
    }
    snprintf(got, cap, "%s", tbuf);
    return strcmp(got, want);
}

/* Прогон встроенных тестов. Возвращает число проваленных. */
static int test_ast(void) {
    int n = sizeof TESTS / sizeof *TESTS, failed = 0;
    static char got[8192];
    for (int i = 0; i < n; i++) {
        bool ok = run_case(TESTS[i].src, TESTS[i].want, got, sizeof got) == 0;
        failed += !ok;
        printf("[%s] %s\n", ok ? "PASS" : "FAIL", TESTS[i].name);
        if (!ok) printf("  получено: %s\n  ожидалось: %s\n", got, TESTS[i].want);
    }
    printf("Пройдено тестов: %d/%d\n", n - failed, n);
    return failed;
}

/* Разбор файлов: печать AST/ошибок и сверка с ожиданием по имени файла. */
static int test_files(int n, char **paths) {
    static char text[1 << 20];
    int failed = 0;
    for (int i = 0; i < n; i++) {
        FILE *f = fopen(paths[i], "rb");
        if (!f) { perror(paths[i]); failed++; continue; }
        size_t len = fread(text, 1, sizeof text, f);
        fclose(f);
        printf("=== %s ===\n", paths[i]);
        int nerr = parse_program(text, len);
        bool want = strstr(paths[i], "bad_missing_semicolon") || strstr(paths[i], "bad_missing_paren");
        bool ok = (nerr > 0) == want;
        failed += !ok;
        printf("[%s] %s: %s\n", ok ? "PASS" : "FAIL", paths[i],
               nerr ? "синтаксические ошибки" : "разбор без ошибок");
    }
    if (n) printf("Файлов с ожидаемым результатом: %d/%d\n", n - failed, n);
    return failed;
}

/* Прогоняет встроенные тесты и разбор указанных файлов. */
int main(int argc, char **argv) {
    out = stdout;
    int failed = test_ast();
    printf("\n");
    failed += test_files(argc - 1, argv + 1);
    return failed ? 1 : 0;
}
