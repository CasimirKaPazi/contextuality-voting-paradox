// Enumerate irreducible totally tight forms (cores: every 2x2 subform has a constant line, no constant
// line, no repeated line) of size m x n with exactly k outcomes, and check that the chain summary of
// each, in both orientations and under every renaming of outcomes, lies inside some starting summary
// of core_chain_starts.py with the same outcomes present.
// Usage: ./core_enum_cover m n k starts_k.txt
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <map>
#include <array>
using namespace std;
typedef uint64_t u64;
int m, n, k; int A[8][8];
int rp[4][8], rq[4][8], pl[4];
map<int, vector<array<u64,4>>> starts;
long ncores = 0, nsumm = 0, bad = 0;
u64 summ(int c, int perm[], bool tr) {
  // lines of player pl[c]: rows (player 0) or columns (player 1) of the (possibly transposed) form
  int R = tr ? n : m, C = tr ? m : n; u64 out = 0;
  auto cell = [&](int r, int s) { return perm[tr ? A[s][r] : A[r][s]]; };
  int L = pl[c] == 0 ? R : C, W = pl[c] == 0 ? C : R;
  for (int l = 0; l < L; l++) {
    int y = -1;
    for (int w = 0; w < W; w++) { int x = pl[c] == 0 ? cell(l, w) : cell(w, l); if (y < 0 || rq[c][x] < rq[c][y]) y = x; }
    int M = -1;
    for (int w = 0; w < W; w++) { int x = pl[c] == 0 ? cell(l, w) : cell(w, l); if (x != y) continue;
      for (int l2 = 0; l2 < L; l2++) { int z = pl[c] == 0 ? cell(l2, w) : cell(w, l2); if (M < 0 || rp[c][z] < rp[c][M]) M = z; } }
    out |= 1ULL << (y * k + M);
  }
  return out;
}
void check() {
  int perm[8]; for (int u = 0; u < k; u++) perm[u] = u;
  do {
    for (int tr = 0; tr < 2; tr++) {
      u64 v[4]; for (int c = 0; c < 4; c++) v[c] = summ(c, perm, tr); nsumm++;
      int pr = (1 << k) - 1; bool ok = false;
      auto it = starts.find(pr);
      if (it != starts.end()) for (auto& s : it->second) { bool sub = true; for (int c = 0; c < 4; c++) if (v[c] & ~s[c]) { sub = false; break; } if (sub) { ok = true; break; } }
      if (!ok) { bad++; if (bad <= 3) { printf("not covered:"); for (int r = 0; r < m; r++) { printf(" "); for (int s = 0; s < n; s++) printf("%d", A[r][s]); } printf("\n"); } }
    }
  } while (next_permutation(perm, perm + k));
}
bool tight2(int r, int c) {
  for (int r2 = 0; r2 < r; r2++) for (int c2 = 0; c2 < n; c2++) { if (c2 == c) continue;
    if (c2 > c) continue;
    int a = A[r2][c2], b = A[r2][c], cc = A[r][c2], d = A[r][c];
    if (!(a == b || cc == d || a == cc || b == d)) return false; }
  return true;
}
void rec(int pos, int maxo) {
  if (pos == m * n) {
    if (maxo != k - 1) return;
    for (int r = 0; r < m; r++) { bool cst = true; for (int s = 1; s < n; s++) if (A[r][s] != A[r][0]) cst = false; if (cst) return; }
    for (int s = 0; s < n; s++) { bool cst = true; for (int r = 1; r < m; r++) if (A[r][s] != A[0][s]) cst = false; if (cst) return; }
    for (int r = 0; r < m; r++) for (int r2 = r + 1; r2 < m; r2++) { bool eq = true; for (int s = 0; s < n; s++) if (A[r][s] != A[r2][s]) eq = false; if (eq) return; }
    for (int s = 0; s < n; s++) for (int s2 = s + 1; s2 < n; s2++) { bool eq = true; for (int r = 0; r < m; r++) if (A[r][s] != A[r][s2]) eq = false; if (eq) return; }
    ncores++; check(); return;
  }
  int r = pos / n, c = pos % n;
  for (int x = 0; x < min(k, maxo + 2); x++) {
    A[r][c] = x;
    if (c == n - 1) { bool cst = true; for (int s = 0; s < n; s++) if (A[r][s] != x) cst = false; if (cst) continue; }
    if (r == m - 1) { bool cst = true; for (int q = 0; q < m; q++) if (A[q][c] != x) cst = false; if (cst) continue; }
    if (tight2(r, c)) rec(pos + 1, max(maxo, x));
  }
}
int main(int argc, char** argv) {
  m = atoi(argv[1]); n = atoi(argv[2]); k = atoi(argv[3]);
  int P[8], rP[8], Ps[8], rPs[8];
  for (int q = 0; q < k; q++) { P[q] = q; rP[q] = k - 1 - q; }
  Ps[0] = 0; for (int q = 0; q + 1 < k; q++) Ps[q + 1] = rP[q];
  rPs[0] = k - 1; for (int q = 0; q + 1 < k; q++) rPs[q + 1] = P[q];
  int* own[4] = {P, rP, Ps, rPs}; int* opp[4] = {rP, P, rP, P}; int pls[4] = {0, 1, 0, 1};
  for (int c = 0; c < 4; c++) { pl[c] = pls[c]; for (int q = 0; q < k; q++) { rp[c][own[c][q]] = q; rq[c][opp[c][q]] = q; } }
  FILE* f = fopen(argv[4], "r"); unsigned long long pr, a, b, cc, d;
  while (fscanf(f, "%llu %llu %llu %llu %llu", &pr, &a, &b, &cc, &d) == 5) starts[(int)pr].push_back({a, b, cc, d});
  rec(0, -1);
  printf("%dx%d, %d outcomes: %ld cores (outcomes in order of first appearance), %ld summaries, %ld not covered\n", m, n, k, ncores, nsumm, bad);
}
