// Exhaustive check of the rational diagonal on all totally reducible two-player game forms
// with k outcomes (any size), via the row-type summary automaton of tr_automaton.py.
// Usage: tr_auto k family   (family: tb = top(P)=bottom(Q), all = every pair, zs+same)
// States are reduced by renaming outcomes; the visited set stores 128-bit hashes.
#include <bits/stdc++.h>
using namespace std;
int k; vector<vector<int>> prefs; vector<vector<int>> rnk;
struct Cfg { int i, a, b; }; vector<Cfg> cfgs; map<tuple<int,int,int>,int> cidx;
int KK;
vector<vector<int>> perms; vector<vector<int>> cperm; vector<vector<uint16_t>> mperm; vector<vector<int>> sperm;
inline int maxP(int a, int x, int y) { return rnk[a][x] <= rnk[a][y] ? x : y; }
inline uint16_t bitt(int y, int M) { return (uint16_t)1 << (y * k + M); }
struct St { vector<uint16_t> m; uint8_t present, F0, F1; };
St step(const St& s, int j, int o) {
  St t; t.m.resize(cfgs.size());
  t.present = s.present | (1 << o);
  uint8_t F[2] = {s.F0, s.F1}; F[1 - j] &= (1 << o); F[j] |= (1 << o); t.F0 = F[0]; t.F1 = F[1];
  for (size_t n = 0; n < cfgs.size(); n++) {
    const Cfg& c = cfgs[n]; uint16_t m = s.m[n], out = 0;
    for (int ty = 0; ty < KK; ty++) if (m >> ty & 1) {
      int y = ty / k, M = ty % k;
      if (j == c.i) out |= bitt(y, maxP(c.a, M, o));
      else out |= (rnk[c.b][o] < rnk[c.b][y]) ? bitt(o, o) : bitt(y, M);
    }
    if (j == c.i) { int best = o; for (int x = 0; x < k; x++) if (t.present >> x & 1) best = maxP(c.a, best, x); out |= bitt(o, best); }
    t.m[n] = out;
  }
  return t;
}
St canon(const St& s) {
  St best; bool have = false; St cand; cand.m.resize(cfgs.size());
  for (size_t p = 0; p < perms.size(); p++) {
    for (size_t n = 0; n < cfgs.size(); n++) cand.m[cperm[p][n]] = mperm[p][s.m[n]];
    cand.present = sperm[p][s.present]; cand.F0 = sperm[p][s.F0]; cand.F1 = sperm[p][s.F1];
    if (!have || tie(cand.present, cand.F0, cand.F1, cand.m) < tie(best.present, best.F0, best.F1, best.m)) { best = cand; have = true; }
  }
  return best;
}
bool valid(const St& s) { return __builtin_popcount(s.present) >= 3 && s.F0 != s.present && s.F1 != s.present; }
bool works(const St& s) {
  for (size_t n = 0; n < cfgs.size(); n++) {
    bool ok = true;
    for (int ty = 0; ty < KK && ok; ty++) if (s.m[n] >> ty & 1) { int y = ty / k, M = ty % k; if (!(rnk[cfgs[n].a][M] < rnk[cfgs[n].a][y])) ok = false; }
    if (ok) return true;
  }
  return false;
}
pair<uint64_t,uint64_t> h(const St& s) {
  uint64_t h1 = 1469598103934665603ULL ^ s.present ^ (s.F0 << 8) ^ ((uint64_t)s.F1 << 16), h2 = 0x9e3779b97f4a7c15ULL ^ h1;
  for (uint16_t x : s.m) { h1 = (h1 ^ x) * 1099511628211ULL; h2 = (h2 + x + 0x7f4a7c15) * 0xff51afd7ed558ccdULL; h2 ^= h2 >> 29; }
  return {h1, h2};
}
struct HH { size_t operator()(const pair<uint64_t,uint64_t>& p) const { return p.first ^ (p.second * 31); } };
int main(int argc, char** argv) {
  k = atoi(argv[1]); string fam = argc > 2 ? argv[2] : "tb"; KK = k * k;
  vector<int> base(k); iota(base.begin(), base.end(), 0);
  do prefs.push_back(base); while (next_permutation(base.begin(), base.end()));
  map<vector<int>,int> pidx; for (size_t n = 0; n < prefs.size(); n++) pidx[prefs[n]] = n;
  for (auto& p : prefs) { vector<int> r(k); for (int q = 0; q < k; q++) r[p[q]] = q; rnk.push_back(r); }
  for (int i = 0; i < 2; i++) for (size_t a = 0; a < prefs.size(); a++) for (size_t b = 0; b < prefs.size(); b++) {
    auto& P = prefs[a]; auto& Q = prefs[b]; bool use;
    vector<int> rev(P.rbegin(), P.rend()), rot(P.begin() + 1, P.end()); rot.push_back(P[0]);
    if (fam == "all") use = true; else if (fam == "tb") use = Q.back() == P[0]; else use = (Q == rev || Q == rot);
    if (use) { cidx[{i, (int)a, (int)b}] = cfgs.size(); cfgs.push_back({i, (int)a, (int)b}); }
  }
  perms = prefs;
  for (auto& pi : perms) {
    vector<int> cp; for (auto& c : cfgs) {
      vector<int> pa(k), pb(k); for (int q = 0; q < k; q++) { pa[q] = pi[prefs[c.a][q]]; pb[q] = pi[prefs[c.b][q]]; }
      cp.push_back(cidx.at({c.i, pidx[pa], pidx[pb]}));
    }
    cperm.push_back(cp);
    vector<uint16_t> mp(1 << KK); for (int m = 0; m < (1 << KK); m++) { uint16_t o = 0; for (int ty = 0; ty < KK; ty++) if (m >> ty & 1) o |= bitt(pi[ty / k], pi[ty % k]); mp[m] = o; }
    mperm.push_back(mp);
    vector<int> sp(1 << k); for (int s = 0; s < (1 << k); s++) { int o = 0; for (int x = 0; x < k; x++) if (s >> x & 1) o |= 1 << pi[x]; sp[s] = o; }
    sperm.push_back(sp);
  }
  fprintf(stderr, "k=%d family=%s configs=%zu\n", k, fam.c_str(), cfgs.size());
  unordered_set<pair<uint64_t,uint64_t>, HH> seen; vector<St> frontier;
  if (argc > 3) {   // start from given summaries (cores: nobody forces a single outcome)
    FILE* f = fopen(argv[3], "r"); int pr;
    while (fscanf(f, "%d", &pr) == 1) {
      St s; s.present = pr; s.F0 = 0; s.F1 = 0; s.m.resize(cfgs.size());
      for (auto& x : s.m) { int v; if (fscanf(f, "%d", &v) != 1) return 1; x = v; }
      s = canon(s); if (seen.insert(h(s)).second) frontier.push_back(s);
    }
    fprintf(stderr, "%zu initial summaries up to renaming\n", frontier.size());
  } else {
    St s0; s0.m.assign(cfgs.size(), bitt(0, 0)); s0.present = 1; s0.F0 = 1; s0.F1 = 1; s0 = canon(s0);
    seen.insert(h(s0)); frontier.push_back(s0);
  }
  long nvalid = 0, bad = 0; int level = 0;
  while (!frontier.empty()) {
    vector<St> nxt;
    for (auto& s : frontier) {
      if (valid(s)) { nvalid++; if (!works(s)) { bad++; if (bad <= 3) { printf("BAD present=%d F=%d,%d level %d\n", s.present, s.F0, s.F1, level); } } }
      for (int j = 0; j < 2; j++) for (int o = 0; o < k; o++) { St t = canon(step(s, j, o)); if (seen.insert(h(t)).second) nxt.push_back(move(t)); }
    }
    frontier.swap(nxt); level++;
    printf("level %d: %zu summaries, %ld valid checked, %ld without a working config\n", level, seen.size(), nvalid, bad); fflush(stdout);
  }
  printf("k=%d family=%s: done. %zu summaries up to renaming, %ld valid, %ld without a working config\n", k, fam.c_str(), seen.size(), nvalid, bad);
}
