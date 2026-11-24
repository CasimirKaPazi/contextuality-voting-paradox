// Note "A tight form without a rational diagonal", Section 7. Local search for tight,
// non-dictatorial n x m forms with k outcomes and few working (player, P, Q), over all strict P, Q.
// Score 0 means no rational diagonal; the form is then printed. Flags: R = require the
// recombination property, V = forbid an outcome forced by both players, - = none.
// Usage: ./local_search n m seed restarts flags k
#include <bits/stdc++.h>
using namespace std;
int n, m, K, NP; vector<vector<int>> perm, rk;
bool optR, optV;
typedef vector<vector<int>> F;
int g(const F& f, int t, int a, int b) { return t == 0 ? f[a][b] : f[b][a]; }
bool works(const F& f, int t, int p, int q) {
  int R = t ? m : n, C = t ? n : m;
  vector<int> best(C, 99);
  for (int b = 0; b < C; b++) for (int a = 0; a < R; a++) best[b] = min(best[b], rk[p][g(f, t, a, b)]);
  for (int a = 0; a < R; a++) {
    int y = -1; for (int b = 0; b < C; b++) { int u = g(f, t, a, b); if (y < 0 || rk[q][u] < rk[q][y]) y = u; }
    bool ref = false; for (int b = 0; b < C && !ref; b++) if (g(f, t, a, b) == y && best[b] < rk[p][y]) ref = true;
    if (!ref) return false;
  }
  return true;
}
int forced(const F& f, int t) { int R = t ? m : n, C = t ? n : m, z = 0;
  for (int a = 0; a < R; a++) { int u = g(f, t, a, 0); bool c = true; for (int b = 1; b < C; b++) if (g(f, t, a, b) != u) c = false; if (c) z |= 1 << u; } return z; }
bool tight(const F& f) {
  for (int S = 1; S < (1 << K) - 1; S++) {
    bool ok = false;
    for (int a = 0; a < n && !ok; a++) { bool in = true; for (int b = 0; b < m; b++) if (!(S >> f[a][b] & 1)) in = false; ok = in; }
    for (int b = 0; b < m && !ok; b++) { bool in = true; for (int a = 0; a < n; a++) if (S >> f[a][b] & 1) in = false; ok = in; }
    if (!ok) return false;
  }
  return true;
}
bool recomb(const F& f) {
  for (int r = 0; r < n; r++) for (int s0 = 0; s0 < m; s0++) for (int r0 = 0; r0 < n; r0++) for (int s = 0; s < m; s++) {
    int x = f[r][s0], y = f[r0][s]; bool ok = false;
    for (int rr = 0; rr < n && !ok; rr++) if (f[rr][s0] == x && f[rr][s] == y) ok = true;
    for (int ss = 0; ss < m && !ok; ss++) if (f[r][ss] == x && f[r0][ss] == y) ok = true;
    if (!ok) return false;
  }
  return true;
}
int score(const F& f) {
  int pres = 0; for (auto& r : f) for (int v : r) pres |= 1 << v;
  if (pres != (1 << K) - 1 || !tight(f)) return 100000;
  int f0 = forced(f, 0), f1 = forced(f, 1);
  if (f0 == (1 << K) - 1 || f1 == (1 << K) - 1) return 100000;
  if (optV && (f0 & f1)) return 100000;
  if (optR && !recomb(f)) return 100000;
  int c = 0; for (int t = 0; t < 2; t++) for (int p = 0; p < NP; p++) for (int q = 0; q < NP; q++) c += works(f, t, p, q);
  return c;
}
int main(int argc, char** argv) {
  n = atoi(argv[1]); m = atoi(argv[2]); mt19937 rng(atoi(argv[3])); int restarts = atoi(argv[4]);
  string fl = argv[5]; optR = fl.find('R') != string::npos; optV = fl.find('V') != string::npos;
  K = atoi(argv[6]); vector<int> pp(K); iota(pp.begin(), pp.end(), 0);
  do perm.push_back(pp); while (next_permutation(pp.begin(), pp.end()));
  NP = perm.size(); rk.assign(NP, vector<int>(K)); for (int p = 0; p < NP; p++) for (int i = 0; i < K; i++) rk[p][perm[p][i]] = i;
  int bestEver = 100000;
  for (int it = 0; it < restarts; it++) {
    F f(n, vector<int>(m)); int s;
    do { for (auto& r : f) for (int& v : r) v = rng() % K; s = score(f); } while (s >= 100000);
    for (int step = 0; step < 20000 && s > 0; step++) {
      F h = f; int k = 1 + rng() % 2; for (int j = 0; j < k; j++) h[rng() % n][rng() % m] = rng() % K;
      int s2 = score(h); if (s2 <= s) { f = h; s = s2; }
    }
    if (s < bestEver) { bestEver = s; printf("restart %d best %d\n", it, s); fflush(stdout); }
    if (s == 0) { for (auto& r : f) { for (int v : r) printf("%c", "abcdefg"[v]); printf("\n"); } fflush(stdout); return 0; }
  }
  printf("none; best %d\n", bestEver);
}
