// The chain on all games of perfect information with k outcomes (k <= 7), of every size.
// The summaries of the four chain configurations (P = (0, ..., k-1), a = 0, c = k-1, i = player 0)
// are closed under composition at a node of either player; tree_summary.py states the rules and
// checks them against normal forms. Only summaries maximal among those with the same outcomes
// present and the same forcing sets are kept: composition is monotone in the pair sets, and a
// working configuration keeps working on a subset, so dropping dominated summaries loses nothing.
// Usage: ./tree_chain k
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <map>
#include <tuple>
using namespace std;
typedef uint64_t u64;
int k; int pl[4], rp[4][8], rq[4][8];
struct St { u64 m[4]; int pr, F0, F1; bool alive; };
vector<St> S; map<tuple<int,int,int>, vector<int>> byKey;
static inline u64 bit(int y, int M) { return 1ULL << (y * k + M); }
int bestOf(int c, int set) { int b = -1; for (int u = 0; u < k; u++) if (set >> u & 1) if (b < 0 || rp[c][u] < rp[c][b]) b = u; return b; }
// pair sets stored per favourite y as a bitmask of M, laid out as bit y*k + M
static inline u64 rowOf(u64 m, int y) { return (m >> (y * k)) & ((1ULL << k) - 1); }
St compose(const St& A, const St& B, int root) {
  St t; t.alive = true;
  for (int c = 0; c < 4; c++) {
    u64 out = 0; u64 a = A.m[c], bb = B.m[c];
    if (root == pl[c]) {
      int bA = bestOf(c, A.pr), bB = bestOf(c, B.pr);
      for (int y = 0; y < k; y++) {
        u64 ra = rowOf(a, y), rb = rowOf(bb, y), o = 0;
        for (int M = 0; M < k; M++) {
          if (ra >> M & 1) o |= 1ULL << (rp[c][bB] < rp[c][M] ? bB : M);
          if (rb >> M & 1) o |= 1ULL << (rp[c][bA] < rp[c][M] ? bA : M);
        }
        out |= o << (y * k);
      }
    } else {
      // worst opponent-rank of a favourite present in A and in B
      int worstA = -1, worstB = -1;
      for (int y = 0; y < k; y++) { if (rowOf(a, y)) worstA = max(worstA, rq[c][y]); if (rowOf(bb, y)) worstB = max(worstB, rq[c][y]); }
      for (int y = 0; y < k; y++) {
        u64 ra = rowOf(a, y), rb = rowOf(bb, y), o = 0;
        if (ra && rq[c][y] < worstB) o |= ra;     // paired with a favourite of B the opponent ranks lower
        if (rb && rq[c][y] < worstA) o |= rb;
        if (ra && rb) {                            // equal favourites: the better M for the owner
          int maxA = -1, maxB = -1;
          for (int M = 0; M < k; M++) { if (ra >> M & 1) maxA = max(maxA, rp[c][M]); if (rb >> M & 1) maxB = max(maxB, rp[c][M]); }
          for (int M = 0; M < k; M++) { if ((ra >> M & 1) && rp[c][M] <= maxB) o |= 1ULL << M; if ((rb >> M & 1) && rp[c][M] <= maxA) o |= 1ULL << M; }
        }
        out |= o << (y * k);
      }
    }
    t.m[c] = out;
  }
  t.pr = A.pr | B.pr;
  if (root == 0) { t.F0 = A.F0 | B.F0; t.F1 = A.F1 & B.F1; } else { t.F1 = A.F1 | B.F1; t.F0 = A.F0 & B.F0; }
  return t;
}
bool sub(const St& a, const St& b) { for (int c = 0; c < 4; c++) if (a.m[c] & ~b.m[c]) return false; return true; }
long insert(const St& t) {   // returns index if kept
  auto key = make_tuple(t.pr, t.F0, t.F1); auto& v = byKey[key];
  for (int i : v) if (S[i].alive && sub(t, S[i])) return -1;
  for (int i : v) if (S[i].alive && sub(S[i], t)) S[i].alive = false;
  S.push_back(t); v.push_back((int)S.size() - 1); return (long)S.size() - 1;
}
bool works(const St& s, int c) {
  for (int y = 0; y < k; y++) for (int M = 0; M < k; M++) if (s.m[c] & bit(y, M)) if (!(rp[c][M] < rp[c][y])) return false;
  return true;
}
int main(int argc, char** argv) {
  k = atoi(argv[1]);
  int P[8], rP[8], Ps[8], rPs[8];
  for (int q = 0; q < k; q++) { P[q] = q; rP[q] = k - 1 - q; }
  Ps[0] = 0; for (int q = 0; q + 1 < k; q++) Ps[q + 1] = rP[q];
  rPs[0] = k - 1; for (int q = 0; q + 1 < k; q++) rPs[q + 1] = P[q];
  int* own[4] = {P, rP, Ps, rPs}; int* opp[4] = {rP, P, rP, P}; int pls[4] = {0, 1, 0, 1};
  for (int c = 0; c < 4; c++) { pl[c] = pls[c]; for (int q = 0; q < k; q++) { rp[c][own[c][q]] = q; rq[c][opp[c][q]] = q; } }
  vector<int> frontier;
  for (int z = 0; z < k; z++) { St s; for (int c = 0; c < 4; c++) s.m[c] = bit(z, z); s.pr = s.F0 = s.F1 = 1 << z; s.alive = true;
    long i = insert(s); if (i >= 0) frontier.push_back((int)i); }
  int rnd = 0;
  while (!frontier.empty()) {
    vector<int> nf; vector<int> live; for (size_t i = 0; i < S.size(); i++) if (S[i].alive) live.push_back((int)i);
    for (auto& kv : byKey) { vector<int> w; for (int i : kv.second) if (S[i].alive) w.push_back(i); kv.second.swap(w); }
    for (int a : frontier) {
      if (!S[a].alive) continue;
      for (int b : live) {
        if (!S[b].alive || !S[a].alive) continue;
        for (int root = 0; root < 2; root++) {
          St A = S[a], B = S[b];
          long i = insert(compose(A, B, root)); if (i >= 0) nf.push_back((int)i);
          i = insert(compose(B, A, root)); if (i >= 0) nf.push_back((int)i);
        }
      }
    }
    long alive = 0; for (auto& s : S) alive += s.alive;
    rnd++; fprintf(stderr, "round %d: %ld maximal summaries (%zu stored), new %zu\n", rnd, alive, S.size(), nf.size());
    frontier.swap(nf);
  }
  long cases = 0, fails = 0, alive = 0;
  for (auto& s : S) { if (!s.alive) continue; alive++;
    if (s.pr == (1 << k) - 1 && !(s.F0 & 1) && !(s.F1 >> (k - 1) & 1)) { cases++;
      if (!(works(s, 0) || works(s, 1) || works(s, 2) || works(s, 3))) fails++; } }
  printf("k=%d: %ld maximal tree summaries, %ld cases, %ld failures\n", k, alive, cases, fails);
}
