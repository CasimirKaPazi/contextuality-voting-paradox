// The chain conjecture on totally tight forms with k <= 7 outcomes, of every size. A summary search
// (Section 3) that tracks only the four configurations of the chain, with P = (0, 1, ..., k-1),
// a = 0, c = k-1 and i = player 0 (by renaming outcomes and swapping players). Exact: states are
// stored in full in an open-addressing table. States are packed into 32 bytes (present and forcing
// sets in the spare high bits), and the symmetry that swaps the players and renames u -> k-1-u
// (configurations 0 <-> 1 and 2 <-> 3) halves them.
// Without a file the search starts from a single cell (stopping games). With a file it starts from
// the pessimistic core summaries written by core_chain_starts.py.
// Usage: ./tr_chain_stop k log2(table size) [starts file], e.g. ./tr_chain_stop 7 27 (about 4 GB)
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
using namespace std;
typedef uint64_t u64;
int k, NB; u64 PAIRS;
struct Cfg { int i; int rp[8], rq[8]; } cf[4];
struct St { u64 m[4]; };   // m[c] low k*k bits: pairs; m[0] high: present, m[1] high: F0, m[2] high: F1
static inline u64 bit(int y, int M) { return 1ULL << (y * k + M); }
static inline int present(const St& s) { return s.m[0] >> NB; }
static inline int F(const St& s, int j) { return s.m[1 + j] >> NB; }
static inline void setHigh(St& s, int c, int v) { s.m[c] = (s.m[c] & PAIRS) | ((u64)v << NB); }
St step(const St& s, int j, int x) {
  St t; int pr = present(s) | 1 << x;
  for (int c = 0; c < 4; c++) {
    const Cfg& C = cf[c]; u64 m = s.m[c] & PAIRS, out = 0;
    if (C.i == j) {
      int best = -1; for (int u = 0; u < k; u++) if (pr >> u & 1) if (best < 0 || C.rp[u] < C.rp[best]) best = u;
      for (int y = 0; y < k; y++) for (int M = 0; M < k; M++) if (m & bit(y, M)) out |= bit(y, C.rp[x] < C.rp[M] ? x : M);
      out |= bit(x, best);
    } else {
      for (int y = 0; y < k; y++) for (int M = 0; M < k; M++) if (m & bit(y, M)) out |= C.rq[x] < C.rq[y] ? bit(x, x) : bit(y, M);
    }
    t.m[c] = out;
  }
  int f0 = F(s, 0), f1 = F(s, 1);
  if (j == 0) { f0 |= 1 << x; f1 &= 1 << x; } else { f1 |= 1 << x; f0 &= 1 << x; }
  setHigh(t, 0, pr); setHigh(t, 1, f0); setHigh(t, 2, f1);
  return t;
}
u64 renPairs(u64 m) { u64 o = 0; for (int y = 0; y < k; y++) for (int M = 0; M < k; M++) if (m & bit(y, M)) o |= bit(k - 1 - y, k - 1 - M); return o; }
int renSet(int v) { int o = 0; for (int u = 0; u < k; u++) if (v >> u & 1) o |= 1 << (k - 1 - u); return o; }
St canon(const St& s) {
  St t; t.m[0] = renPairs(s.m[1] & PAIRS); t.m[1] = renPairs(s.m[0] & PAIRS); t.m[2] = renPairs(s.m[3] & PAIRS); t.m[3] = renPairs(s.m[2] & PAIRS);
  setHigh(t, 0, renSet(present(s))); setHigh(t, 1, renSet(F(s, 1))); setHigh(t, 2, renSet(F(s, 0)));
  return memcmp(&t, &s, sizeof(St)) < 0 ? t : s;
}
bool works(const St& s, int c) {
  const Cfg& C = cf[c]; u64 m = s.m[c] & PAIRS;
  for (int y = 0; y < k; y++) for (int M = 0; M < k; M++) if (m & bit(y, M)) if (!(C.rp[M] < C.rp[y])) return false;
  return true;
}
bool chainOK(const St& s) { return works(s, 0) || works(s, 1) || works(s, 2) || works(s, 3); }
St* T; u64 MASK; u64 nstates = 0;
static inline u64 hsh(const St& s) { u64 h = 0x9E3779B97F4A7C15ULL; for (int c = 0; c < 4; c++) { h ^= s.m[c]; h *= 0xff51afd7ed558ccdULL; h ^= h >> 32; } return h; }
long insert(const St& s) {   // returns slot if new, -1 if present
  u64 i = hsh(s) & MASK;
  while (true) {
    St& e = T[i];
    if (e.m[0] == 0 && e.m[1] == 0 && e.m[2] == 0 && e.m[3] == 0) { e = s; nstates++; return (long)i; }
    if (memcmp(&e, &s, sizeof(St)) == 0) return -1;
    i = (i + 1) & MASK;
  }
}
int main(int argc, char** argv) {
  k = atoi(argv[1]); int lg = atoi(argv[2]); NB = k * k; PAIRS = (NB >= 64) ? ~0ULL : ((1ULL << NB) - 1);
  if (NB + k > 64) { fprintf(stderr, "k too large\n"); return 1; }
  int P[8], rP[8], Ps[8], rPs[8];
  for (int q = 0; q < k; q++) { P[q] = q; rP[q] = k - 1 - q; }
  Ps[0] = 0; for (int q = 0; q + 1 < k; q++) Ps[q + 1] = rP[q];
  rPs[0] = k - 1; for (int q = 0; q + 1 < k; q++) rPs[q + 1] = P[q];
  auto setc = [&](int c, int i, int* own, int* opp) { cf[c].i = i; for (int q = 0; q < k; q++) { cf[c].rp[own[q]] = q; cf[c].rq[opp[q]] = q; } };
  setc(0, 0, P, rP); setc(1, 1, rP, P); setc(2, 0, Ps, rP); setc(3, 1, rPs, P);
  u64 size = 1ULL << lg; MASK = size - 1; T = (St*)calloc(size, sizeof(St));
  if (!T) { fprintf(stderr, "no memory\n"); return 1; }
  vector<uint32_t> fr, nx;
  if (argc > 3) {
    FILE* f = fopen(argv[3], "r"); unsigned long long pr, m0, m1, m2, m3; long nstart = 0;
    while (fscanf(f, "%llu %llu %llu %llu %llu", &pr, &m0, &m1, &m2, &m3) == 5) {
      St s; s.m[0] = m0; s.m[1] = m1; s.m[2] = m2; s.m[3] = m3;
      setHigh(s, 0, (int)pr); setHigh(s, 1, 0); setHigh(s, 2, 0);
      long i = insert(canon(s)); if (i >= 0) fr.push_back((uint32_t)i); nstart++; }
    fprintf(stderr, "%ld starting summaries read\n", nstart);
  } else
  for (int z = 0; z < k; z++) { St s; for (int c = 0; c < 4; c++) s.m[c] = bit(z, z);
    setHigh(s, 0, 1 << z); setHigh(s, 1, 1 << z); setHigh(s, 2, 1 << z);
    long i = insert(canon(s)); if (i >= 0) fr.push_back((uint32_t)i); }
  long cases = 0, fails = 0; int level = 0; int all = (1 << k) - 1;
  while (!fr.empty()) {
    nx.clear();
    for (uint32_t idx : fr) {
      St s = T[idx];
      if (present(s) == all) {
        // the state stands for itself and for its mirror image; check the chain on both
        for (int pass = 0; pass < 2; pass++) {
          St u = s;
          if (pass == 1) { St t; t.m[0] = renPairs(s.m[1] & PAIRS); t.m[1] = renPairs(s.m[0] & PAIRS); t.m[2] = renPairs(s.m[3] & PAIRS); t.m[3] = renPairs(s.m[2] & PAIRS);
            setHigh(t, 0, renSet(present(s))); setHigh(t, 1, renSet(F(s, 1))); setHigh(t, 2, renSet(F(s, 0))); u = t; }
          if (!(F(u, 0) & 1) && !(F(u, 1) >> (k - 1) & 1)) {
            cases++; if (!chainOK(u)) { fails++; if (fails <= 3) printf("FAIL at level %d: present %d F %d %d m %llu %llu %llu %llu\n", level, present(u), F(u,0), F(u,1), (unsigned long long)(u.m[0]&PAIRS), (unsigned long long)(u.m[1]&PAIRS), (unsigned long long)(u.m[2]&PAIRS), (unsigned long long)(u.m[3]&PAIRS)); } }
        }
      }
      for (int j = 0; j < 2; j++) for (int x = 0; x < k; x++) {
        long i = insert(canon(step(s, j, x))); if (i >= 0) nx.push_back((uint32_t)i);
        if (nstates > size * 0.85) { fprintf(stderr, "table full\n"); return 2; } }
    }
    fr.swap(nx); level++;
    fprintf(stderr, "level %d: %llu summaries, frontier %zu\n", level, (unsigned long long)nstates, fr.size());
  }
  printf("k=%d: %llu summaries up to the player symmetry, %ld cases, %ld failures\n", k, (unsigned long long)nstates, cases, fails);
}
