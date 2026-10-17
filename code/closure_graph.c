/* closure_graph.c -- the closure graph of Sect. III of the paper, in C.
   Build: cc -O2 -o closure_graph_c closure_graph.c && ./closure_graph_c */
#include <stdio.h>
#include <string.h>
enum { HC, F3, F2, F3p, L, M, V, AB, NS };
static const char *NAME[NS] = {"HC","F3","F2","F3p","L","M","V","AB"};
static const int RULEP[12][2] = {{HC,-1},{F3,-1},{HC,-1},{HC,-1},{HC,-1},{F2,-1},
                                 {AB,-1},{AB,F3p},{L,M},{L,-1},{V,-1},{HC,-1}};
static const int RULEC[12] = {F3,HC,F2,F3p,AB,AB,F2,HC,HC,AB,AB,M};
static int closure(int m) {
    for (;;) {
        int n = m;
        for (int r = 0; r < 12; r++) {
            int pm = 1 << RULEP[r][0];
            if (RULEP[r][1] >= 0) pm |= 1 << RULEP[r][1];
            if ((m & pm) == pm) n |= 1 << RULEC[r];
        }
        if (n == m) return m;
        m = n;
    }
}
static void pr(int m) {
    printf("  {"); int first = 1;
    for (int i = 0; i < NS; i++) if (m & (1 << i)) { printf("%s%s", first ? "" : ",", NAME[i]); first = 0; }
    printf("}\n");
}
int main(void) {
    int derive[256], nd = 0, minimal[256], nm = 0, ok = 1;
    for (int m = 0; m < 256; m++) { derive[m] = (closure(m) >> HC) & 1; nd += derive[m]; }
    for (int m = 0; m < 256; m++) {
        if (m & (1 << HC) || !derive[m]) continue;
        int min = 1;
        for (int t = 0; t < 256; t++) if (t != m && (t & m) == t && !(t & (1 << HC)) && derive[t]) min = 0;
        if (min) minimal[nm++] = m;
    }
    printf("subsets: 256  deriving HC: %d\nminimal sufficient sets: %d\n", nd, nm);
    const int expected[6] = {1<<F3, (1<<L)|(1<<M), (1<<L)|(1<<F3p), (1<<V)|(1<<F3p), (1<<F2)|(1<<F3p), (1<<AB)|(1<<F3p)};
    if (nm != 6) ok = 0;
    for (int i = 0; i < 6; i++) { int f = 0; for (int j = 0; j < nm; j++) if (minimal[j] == expected[i]) f = 1; if (!f) ok = 0; }
    for (int j = 0; j < nm; j++) pr(minimal[j]);
    const int neg[8] = {1<<F2, 1<<F3p, 1<<L, 1<<M, 1<<V, 1<<AB, (1<<L)|(1<<V), (1<<M)|(1<<F3p)};
    for (int i = 0; i < 8; i++) if (derive[neg[i]]) ok = 0;
    printf("closure_graph.c: %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}
