// Note "A tight form without a rational diagonal", Section 3. A form with a constant row c and a
// constant column c (c = 2) is tight. For every inner form G (n x m, outcomes 0, 1, 2), add a
// c-row and a c-column and test whether some player works under some strict P, Q, that is, has
// no strict Nash strategy. Prints the inner forms where nobody does (non-dictatorial, all three
// outcomes present). Inner forms are numbered in base 3, row-major; [from to) restricts the range.
// Usage: ./border_scan n m [from to]
#include <cstdio>
#include <cstdlib>
#include <vector>
using namespace std;
int n, m, N, M; int F[8][8];
int perm[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
int rk[6][3];
inline int g(int t, int a, int b) { return t == 0 ? F[a][b] : F[b][a]; }  // player t's view: rows a
bool works(int t, int p, int q) {
  int R = t == 0 ? N : M, Cc = t == 0 ? M : N;
  const int* rp = rk[p]; const int* rq = rk[q];
  // best (lowest rank) for i in each column
  int best[8]; for (int b = 0; b < Cc; b++) { int v = 9; for (int a = 0; a < R; a++) v = min(v, rp[g(t, a, b)]); best[b] = v; }
  for (int a = 0; a < R; a++) {
    int y = -1; for (int b = 0; b < Cc; b++) { int u = g(t, a, b); if (y < 0 || rq[u] < rq[y]) y = u; }
    bool ref = false;
    for (int b = 0; b < Cc && !ref; b++) if (g(t, a, b) == y && best[b] < rp[y]) ref = true;
    if (!ref) return false;
  }
  return true;
}
int main(int argc, char** argv) {
  n = atoi(argv[1]); m = atoi(argv[2]); N = n + 1; M = m + 1;
  for (int p = 0; p < 6; p++) for (int q = 0; q < 3; q++) rk[p][perm[p][q]] = q;
  long total = 1; for (int i = 0; i < n * m; i++) total *= 3;
  long found = 0, valid = 0;
  for (int b = 0; b < M; b++) F[0][b] = 2; for (int a = 0; a < N; a++) F[a][0] = 2;
  long lo = argc > 3 ? atol(argv[3]) : 0, hi = argc > 4 ? atol(argv[4]) : total;
  for (long code = lo; code < hi; code++) {
    long c = code; int pres = 0;
    for (int a = 1; a < N; a++) for (int b = 1; b < M; b++) { F[a][b] = c % 3; c /= 3; pres |= 1 << F[a][b]; }
    if ((pres & 3) != 3) continue;
    // dictator: some player has constant lines of every outcome (c already); check a and b
    bool dict = false;
    for (int t = 0; t < 2 && !dict; t++) { int R = t == 0 ? N : M, Cc = t == 0 ? M : N, fz = 0;
      for (int a = 0; a < R; a++) { int u = g(t, a, 0); bool cst = true; for (int bb = 1; bb < Cc; bb++) if (g(t, a, bb) != u) { cst = false; break; } if (cst) fz |= 1 << u; }
      if (fz == 7) dict = true; }
    if (dict) continue;
    valid++;
    bool any = false;
    for (int t = 0; t < 2 && !any; t++) for (int p = 0; p < 6 && !any; p++) for (int q = 0; q < 6 && !any; q++) if (works(t, p, q)) any = true;
    if (!any) { found++; if (found <= 5) { printf("inner:"); for (int a = 1; a < N; a++) { printf(" "); for (int b = 1; b < M; b++) printf("%d", F[a][b]); } printf("\n"); } }
  }
  printf("n=%d m=%d: %ld valid inner forms, %ld without a rational diagonal\n", n, m, valid, found);
}
