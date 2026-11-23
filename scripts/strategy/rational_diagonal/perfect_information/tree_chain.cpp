// The chain on all games of perfect information with k outcomes (k <= 7), by closing the leaf
// summaries under composition at a node of either player (tree_summary.py gives the rules).
// Only summaries that are maximal among those with the same outcomes present and the same two
// forcing bits are kept: composition is monotone in the pair sets and a working configuration
// keeps working on a subset, so dropping dominated summaries loses nothing.
// The chain reads only two forcing facts: whether player 0 forces outcome 0 and whether player 1
// forces outcome k-1. Forcing composes bitwise (union at the forcing player's node, intersection
// at the other player's), so these two bits compose on their own.
// Composition is symmetric in its two subtrees, so each unordered pair is composed once.
// Build: g++ -O2 -fopenmp -o tree_chain tree_chain.cpp (without -fopenmp it runs on one thread)
// Usage: ./tree_chain k
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <unordered_set>
using namespace std;
typedef uint64_t u64;
int k; int pl[4], rp[4][8], rq[4][8];
struct St { u64 m[4]; int pr, f; bool alive; };   // f: bit 0 = player 0 forces 0, bit 1 = player 1 forces k-1
vector<St> S; vector<vector<int>> byKey;
u64 rowMask, rep;                 // one row of k bits; the low bit of every row
int best[4][256];                  // owner-best outcome of a presence set
u64 keepRep[4][8];                 // M ranked no worse than b, replicated in every row
int maxr[4][256];                  // worst owner rank of M in a row mask
u64 lowRow[4][9];                  // M with owner rank <= r (one row)
static inline u64 rowOf(u64 m, int y) { return (m >> (y * k)) & rowMask; }
// rows of m that are nonzero, as a k-bit mask of y
static inline int nz(u64 m) { int r = 0; for (int y = 0; y < k; y++) if (rowOf(m, y)) r |= 1 << y; return r; }
St compose(const St& A, const St& B, int root) {
  St t; t.alive = true;
  for (int c = 0; c < 4; c++) {
    u64 out = 0, a = A.m[c], bb = B.m[c];
    if (root == pl[c]) {
      int bA = best[c][A.pr], bB = best[c][B.pr];
      // pairs of A: M kept if the owner ranks it no worse than bB, else replaced by bB
      u64 ka = a & keepRep[c][bB], da = a & ~keepRep[c][bB];
      u64 kb = bb & keepRep[c][bA], db = bb & ~keepRep[c][bA];
      out = ka | kb;
      for (int y = 0; y < k; y++) {
        if (rowOf(da, y)) out |= 1ULL << (y * k + bB);
        if (rowOf(db, y)) out |= 1ULL << (y * k + bA);
      }
    } else {
      int worstA = -1, worstB = -1;
      int na = nz(a), nb = nz(bb);
      for (int y = 0; y < k; y++) { if (na >> y & 1) worstA = max(worstA, rq[c][y]); if (nb >> y & 1) worstB = max(worstB, rq[c][y]); }
      for (int y = 0; y < k; y++) {
        u64 ra = rowOf(a, y), rb = rowOf(bb, y), o = 0;
        if (ra && rq[c][y] < worstB) o |= ra;   // paired with a favourite of B the opponent ranks lower
        if (rb && rq[c][y] < worstA) o |= rb;
        if (ra && rb) o |= (ra & lowRow[c][maxr[c][rb]]) | (rb & lowRow[c][maxr[c][ra]]);  // equal favourites
        out |= o << (y * k);
      }
    }
    t.m[c] = out;
  }
  t.pr = A.pr | B.pr;
  int f0a = A.f & 1, f0b = B.f & 1, f1a = A.f >> 1 & 1, f1b = B.f >> 1 & 1;
  if (root == 0) t.f = (f0a | f0b) | ((f1a & f1b) << 1); else t.f = (f0a & f0b) | ((f1a | f1b) << 1);
  return t;
}
static inline bool sub(const St& a, const St& b) { for (int c = 0; c < 4; c++) if (a.m[c] & ~b.m[c]) return false; return true; }
// every summary ever met: one met before is equal to or dominated by a kept one
struct H { size_t operator()(const St& s) const { u64 h = s.pr * 4 + s.f; for (int c = 0; c < 4; c++) h = h * 0x9E3779B97F4A7C15ULL ^ s.m[c]; return h ^ (h >> 29); } };
struct E { bool operator()(const St& a, const St& b) const { return a.pr == b.pr && a.f == b.f && a.m[0] == b.m[0] && a.m[1] == b.m[1] && a.m[2] == b.m[2] && a.m[3] == b.m[3]; } };
unordered_set<St, H, E> seen;
long insert(const St& t) {
  if (!seen.insert(t).second) return -1;
  auto& v = byKey[t.pr * 4 + t.f];
  size_t w = 0;
  for (size_t j = 0; j < v.size(); j++) { int i = v[j]; if (!S[i].alive) continue; v[w++] = i; if (sub(t, S[i])) { for (size_t r = j + 1; r < v.size(); r++) v[w++] = v[r]; v.resize(w); return -1; } }
  v.resize(w);
  for (int i : v) if (sub(S[i], t)) S[i].alive = false;
  S.push_back(t); v.push_back((int)S.size() - 1); return (long)S.size() - 1;
}
bool works(const St& s, int c) {
  for (int y = 0; y < k; y++) for (int M = 0; M < k; M++) if (s.m[c] >> (y * k + M) & 1) if (!(rp[c][M] < rp[c][y])) return false;
  return true;
}
int main(int argc, char** argv) {
  k = atoi(argv[1]);
  rowMask = (1ULL << k) - 1; rep = 0; for (int y = 0; y < k; y++) rep |= 1ULL << (y * k);
  int P[8], rP[8], Ps[8], rPs[8];
  for (int q = 0; q < k; q++) { P[q] = q; rP[q] = k - 1 - q; }
  Ps[0] = 0; for (int q = 0; q + 1 < k; q++) Ps[q + 1] = rP[q];
  rPs[0] = k - 1; for (int q = 0; q + 1 < k; q++) rPs[q + 1] = P[q];
  int* own[4] = {P, rP, Ps, rPs}; int* opp[4] = {rP, P, rP, P}; int pls[4] = {0, 1, 0, 1};
  for (int c = 0; c < 4; c++) { pl[c] = pls[c]; for (int q = 0; q < k; q++) { rp[c][own[c][q]] = q; rq[c][opp[c][q]] = q; } }
  for (int c = 0; c < 4; c++) {
    for (int s = 0; s < (1 << k); s++) { int b = -1, w = -1;
      for (int u = 0; u < k; u++) if (s >> u & 1) { if (b < 0 || rp[c][u] < rp[c][b]) b = u; w = max(w, rp[c][u]); }
      best[c][s] = b; maxr[c][s] = w; }
    for (int b = 0; b < k; b++) { u64 row = 0; for (int M = 0; M < k; M++) if (rp[c][M] <= rp[c][b]) row |= 1ULL << M; keepRep[c][b] = row * rep; }
    for (int r = 0; r <= k; r++) { u64 row = 0; for (int M = 0; M < k; M++) if (rp[c][M] <= r) row |= 1ULL << M; lowRow[c][r] = row; }
  }
  byKey.assign((1 << k) * 4, {});
  vector<int> frontier;
  for (int z = 0; z < k; z++) { St s; for (int c = 0; c < 4; c++) s.m[c] = 1ULL << (z * k + z);
    s.pr = 1 << z; s.f = (z == 0 ? 1 : 0) | (z == k - 1 ? 2 : 0); s.alive = true;
    long i = insert(s); if (i >= 0) frontier.push_back((int)i); }
  int rnd = 0;
  while (!frontier.empty()) {
    vector<int> live; for (size_t i = 0; i < S.size(); i++) if (S[i].alive) live.push_back((int)i);
    for (auto& v : byKey) { vector<int> w; for (int i : v) if (S[i].alive) w.push_back(i); v.swap(w); }
    vector<char> inF(S.size(), 0); for (int a : frontier) inF[a] = 1;
    vector<int> nf;
    const size_t CH = 64;
    for (size_t f0 = 0; f0 < frontier.size(); f0 += CH) {
      size_t f1 = min(frontier.size(), f0 + CH);
      vector<vector<St>> buf(f1 - f0);
      #pragma omp parallel for schedule(dynamic)
      for (size_t fi = f0; fi < f1; fi++) {
        int a = frontier[fi]; if (!S[a].alive) continue;
        auto& out = buf[fi - f0];
        for (int b : live) {
          if (!S[b].alive) continue;
          if (inF[b] && b < a) continue;        // unordered pair composed once
          for (int root = 0; root < 2; root++) out.push_back(compose(S[a], S[b], root));
        }
      }
      for (auto& out : buf) for (auto& t : out) { long i = insert(t); if (i >= 0) nf.push_back((int)i); }
    }
    long alive = 0; for (auto& s : S) alive += s.alive;
    rnd++; fprintf(stderr, "round %d: %ld maximal summaries (%zu stored), new %zu\n", rnd, alive, S.size(), nf.size());
    frontier.swap(nf);
  }
  long cases = 0, fails = 0, alive = 0;
  for (auto& s : S) { if (!s.alive) continue; alive++;
    if (s.pr == (1 << k) - 1 && !(s.f & 1) && !(s.f & 2)) { cases++;
      if (!(works(s, 0) || works(s, 1) || works(s, 2) || works(s, 3))) fails++; } }
  printf("k=%d: %ld maximal tree summaries, %ld cases, %ld failures\n", k, alive, cases, fails);
}
