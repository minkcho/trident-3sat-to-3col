/*
 * check_small_gadgets.c: an independent check of the smallest valid clause
 * gadgets for the reduction from 3SAT to 3-coloring when no symmetry is
 * required (see README.md in this folder).
 *
 * Vertices, as in the root README: the literals x0 x1 x2 are 0 1 2, the
 * palette anchors G_T G_F G_B are 3 4 5, and the auxiliary vertices a1, a2,
 * ... are 6, 7, .... The anchors are colored T, F, B (0, 1, 2). Under an
 * input, a true literal gets the color T and a false one the color F.
 *
 * A gadget is valid if a proper 3-coloring exists for exactly the seven
 * inputs that satisfy (x0 or x1 or x2). The palette triangle and the edges
 * x_i -- G_B are always present; they never conflict with these colors.
 *
 * Candidate edges: every pair with an auxiliary endpoint, binom(k,2) + 6k
 * pairs for k auxiliary vertices. No other pair can be an edge of a valid
 * gadget: an edge between two literals rejects (T,T,T), an edge x_i -- G_T
 * rejects the input in which only x_i is true, and an edge x_i -- G_F
 * rejects the input in which only x_i is false.
 *
 * Search: the candidate edges are decided one by one. Adding an edge can
 * only remove proper colorings, so a branch is cut as soon as a satisfying
 * input has none left. For k = 0, ..., 4 the program prints the number of
 * valid gadgets, the number up to relabeling the auxiliary vertices, and the
 * classes up to relabeling the auxiliary vertices and the literals. Then it
 * checks the five gadgets of the figure.
 *
 * Build and run:  cc -O2 -o check_small_gadgets check_small_gadgets.c
 *                 ./check_small_gadgets
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXK 4
#define NV (6 + MAXK)
#define MAXE 30                   /* binom(4,2) + 6 * 4 */
#define MAXW ((8 * 81 + 63) / 64) /* (input, coloring) pairs in 64-bit words */

static int K, NC, W, NE; /* auxiliary vertices, 3^K colorings, words, edges */
static int eu[MAXE], ev[MAXE], eidx[NV][NV];
static uint64_t bad[MAXE][MAXW]; /* pairs (input, coloring) edge e makes improper */
static uint64_t all[8][MAXW];    /* all pairs of an input */
static uint64_t *found;
static size_t nfound, capfound;
static long long accepting; /* edge sets that accept every satisfying input */

/* color of vertex v under an input (bit i = x_i true) and a coloring c of
   the auxiliary vertices (base-3 digits) */
static int color(int v, int input, int c) {
  if (v < 3) return (input >> v & 1) ? 0 : 1;
  if (v < 6) return v - 3;
  for (int j = v - 6; j > 0; j--) c /= 3;
  return c % 3;
}

/* no proper coloring is left for this input */
static int rejected(const uint64_t *u, int input) {
  for (int w = 0; w < W; w++)
    if ((u[w] & all[input][w]) != all[input][w]) return 0;
  return 1;
}

static void search(int e, const uint64_t *u, uint64_t set) {
  for (int input = 1; input < 8; input++)
    if (rejected(u, input)) return;
  if (e == NE) {
    accepting++;
    if (rejected(u, 0)) { /* (F,F,F) is rejected: valid */
      if (nfound == capfound) {
        capfound = capfound ? 2 * capfound : 1024;
        found = realloc(found, capfound * sizeof *found);
        if (!found) { perror("realloc"); exit(1); }
      }
      found[nfound++] = set;
    }
    return;
  }
  search(e + 1, u, set);
  uint64_t v[MAXW];
  for (int w = 0; w < W; w++) v[w] = u[w] | bad[e][w];
  search(e + 1, v, set | (uint64_t)1 << e);
}

static void add_edge(int a, int b) {
  eu[NE] = a; ev[NE] = b;
  eidx[a][b] = eidx[b][a] = NE++;
}

static void setup(int k) {
  K = k; NC = 1;
  for (int j = 0; j < k; j++) NC *= 3;
  W = (8 * NC + 63) / 64;
  NE = 0;
  for (int i = 0; i < k; i++)
    for (int j = i + 1; j < k; j++) add_edge(6 + i, 6 + j);
  for (int i = 0; i < k; i++)
    for (int v = 0; v < 6; v++) add_edge(v, 6 + i);
  memset(bad, 0, sizeof bad);
  memset(all, 0, sizeof all);
  for (int input = 0; input < 8; input++)
    for (int c = 0; c < NC; c++) {
      int p = input * NC + c;
      all[input][p / 64] |= (uint64_t)1 << (p % 64);
      for (int e = 0; e < NE; e++)
        if (color(eu[e], input, c) == color(ev[e], input, c))
          bad[e][p / 64] |= (uint64_t)1 << (p % 64);
    }
}

/* relabelings: permutations of the auxiliary vertices and of the literals */
static int auxperm[24][MAXK], nauxperm, litperm[6][3];

static void aux_perms(int *p, int depth, int k, int used) {
  if (depth == k) { memcpy(auxperm[nauxperm++], p, sizeof(int) * MAXK); return; }
  for (int x = 0; x < k; x++)
    if (!(used >> x & 1)) { p[depth] = x; aux_perms(p, depth + 1, k, used | 1 << x); }
}

static void make_perms(int k) {
  int n = 0, p[MAXK] = {0};
  for (int a = 0; a < 3; a++)
    for (int b = 0; b < 3; b++)
      for (int c = 0; c < 3; c++)
        if (a != b && a != c && b != c) { litperm[n][0] = a; litperm[n][1] = b; litperm[n][2] = c; n++; }
  nauxperm = 0;
  aux_perms(p, 0, k, 0);
}

static int image(int v, const int *lp, const int *ap) {
  if (v < 3) return lp[v];
  if (v < 6) return v;
  return 6 + ap[v - 6];
}

static uint64_t relabel(uint64_t set, const int *lp, const int *ap) {
  uint64_t r = 0;
  for (int e = 0; e < NE; e++)
    if (set >> e & 1) r |= (uint64_t)1 << eidx[image(eu[e], lp, ap)][image(ev[e], lp, ap)];
  return r;
}

/* the smallest relabeled edge set: one name per class */
static uint64_t canonical(uint64_t set, int literals_too) {
  static const int id[3] = {0, 1, 2};
  uint64_t best = UINT64_MAX;
  for (int l = 0; l < (literals_too ? 6 : 1); l++)
    for (int q = 0; q < nauxperm; q++) {
      uint64_t r = relabel(set, literals_too ? litperm[l] : id, auxperm[q]);
      if (r < best) best = r;
    }
  return best;
}

static int popcount(uint64_t x) {
  int n = 0;
  for (; x; x &= x - 1) n++;
  return n;
}

static int by_value(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return (x > y) - (x < y);
}

static int by_size(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  int d = popcount(x) - popcount(y);
  return d ? d : (x > y) - (x < y);
}

static size_t unique(uint64_t *v, size_t n) {
  size_t m = 0;
  qsort(v, n, sizeof *v, by_value);
  for (size_t i = 0; i < n; i++)
    if (m == 0 || v[i] != v[m - 1]) v[m++] = v[i];
  return m;
}

static int valid(uint64_t set) {
  uint64_t u[MAXW] = {0};
  for (int e = 0; e < NE; e++)
    if (set >> e & 1)
      for (int w = 0; w < W; w++) u[w] |= bad[e][w];
  for (int input = 1; input < 8; input++)
    if (rejected(u, input)) return 0;
  return rejected(u, 0);
}

static const char *commas(long long x, char *buf) {
  char t[32];
  int n = snprintf(t, sizeof t, "%lld", x), o = 0;
  for (int i = 0; i < n; i++) {
    buf[o++] = t[i];
    if (i < n - 1 && (n - 1 - i) % 3 == 0) buf[o++] = ',';
  }
  buf[o] = 0;
  return buf;
}

static const char *name(int v) {
  static const char *names[NV] = {"x0", "x1", "x2", "G_T", "G_F", "G_B", "a1", "a2", "a3", "a4"};
  return names[v];
}

/* the five gadgets of the figure, panels (a) to (e) */
enum { X0, X1, X2, GT, GF, GB, A1, A2, A3, A4 };
static const int panel[5][10][2] = {
  {{A1, A2}, {A2, A3}, {A3, A4}, {A1, GT}, {A4, GT}, {A2, GF}, {A1, X1}, {A2, X1}, {A3, X0}, {A4, X2}},
  {{A1, A2}, {A2, A3}, {A3, A4}, {A1, GT}, {A4, GT}, {A3, GF}, {A1, X1}, {A2, X0}, {A4, X2}, {-1, -1}},
  {{A1, A2}, {A2, A3}, {A3, A4}, {A1, GT}, {A4, GT}, {A1, X0}, {A1, X1}, {A2, X0}, {A3, X1}, {A4, X2}},
  {{A1, A2}, {A2, A3}, {A3, A4}, {A1, GT}, {A4, GT}, {A1, X0}, {A2, X0}, {A3, X1}, {A4, X2}, {-1, -1}},
  {{A1, A2}, {A2, A3}, {A3, A4}, {A1, GT}, {A4, GT}, {A1, X0}, {A2, X1}, {A3, X0}, {A4, X2}, {-1, -1}},
};

int main(void) {
  char b1[32], b2[32];
  uint64_t classes[64];
  size_t nclasses = 0;
  for (int k = 0; k <= MAXK; k++) {
    uint64_t u[MAXW] = {0};
    setup(k);
    make_perms(k);
    nfound = 0;
    accepting = 0;
    search(0, u, 0);
    printf("k = %d: %d candidate edges, 2^%d edge sets; %s accept every satisfying input, "
           "%s of them also reject (F,F,F): valid\n",
           k, NE, NE, commas(accepting, b1), commas((long long)nfound, b2));
    if (nfound == 0) continue;
    uint64_t *aux = malloc(nfound * sizeof *aux), *full = malloc(nfound * sizeof *full);
    if (!aux || !full) { perror("malloc"); return 1; }
    for (size_t i = 0; i < nfound; i++) {
      aux[i] = canonical(found[i], 0);
      full[i] = canonical(found[i], 1);
    }
    size_t naux = unique(aux, nfound);
    nclasses = unique(full, nfound);
    qsort(full, nclasses, sizeof *full, by_size);
    printf("       %zu up to relabeling the auxiliary vertices\n", naux);
    printf("       %zu classes up to relabeling the auxiliary vertices and the literals:\n", nclasses);
    for (size_t c = 0; c < nclasses && c < 64; c++) {
      int members = 0;
      for (size_t i = 0; i < naux; i++)
        if (canonical(aux[i], 1) == full[c]) members++;
      classes[c] = full[c];
      printf("         class %zu: %d edges, %d gadgets up to relabeling the auxiliary vertices\n",
             c + 1, popcount(full[c]), members);
    }
    free(aux);
    free(full);
  }

  /* K = 4 is still set up: check the gadgets of the figure */
  printf("\nThe gadgets of the figure (edges other than the palette triangle and x_i -- G_B):\n");
  int ok = 1, seen[64] = {0};
  for (int p = 0; p < 5; p++) {
    uint64_t set = 0;
    for (int i = 0; i < 10 && panel[p][i][0] >= 0; i++)
      set |= (uint64_t)1 << eidx[panel[p][i][0]][panel[p][i][1]];
    uint64_t c = canonical(set, 1);
    int cls = -1;
    for (size_t j = 0; j < nclasses; j++)
      if (classes[j] == c) cls = (int)j;
    int v = valid(set);
    printf("  (%c) %2d edges, %s, class %d:", 'a' + p, popcount(set), v ? "valid" : "NOT VALID", cls + 1);
    for (int e = 0; e < NE; e++)
      if (set >> e & 1) printf(" %s-%s", name(eu[e]), name(ev[e]));
    printf("\n");
    if (!v || cls < 0 || seen[cls]++) ok = 0;
  }
  if (ok && nclasses == 5)
    printf("All five are valid and lie in different classes: the figure shows one gadget of every class.\n");
  else
    printf("MISMATCH between the figure and the search.\n");
  return ok && nclasses == 5 ? 0 : 1;
}
