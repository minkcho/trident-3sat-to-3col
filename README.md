# trident-3sat-to-3col

The exhaustive enumeration behind Section IV-D of

> M. Cho, H. Kim, and I. Shin, "The Trident: A Minimum Symmetric Clause
> Gadget for 3SAT to 3-Coloring."

The paper proves that the trident is the unique minimum S3-symmetric clause
gadget for the reduction from 3SAT to graph 3-coloring (Theorem 16). This
program confirms it by machine: among all S3-symmetric candidate gadgets with
at most twelve vertices, the only valid one is the trident.

The enumeration is two files of Lean 4, with no dependencies:

- `Color.lean`: the 3-coloring check (is a gadget valid?)
- `Sweep.lean`: the loop (every candidate, composition by composition)

## Run

Install [elan](https://github.com/leanprover/elan); the Lean version is
pinned in `lean-toolchain`.

```bash
lake build
lake exe sweep --test          # the numbers and gadgets quoted in the paper
lake exe sweep --max=6         # compositions with a size-3 or free orbit, N <= 12
lake exe sweep --max=6 --all   # every orbit composition, N <= 12
```

`--max=K` grows the number of auxiliary vertices from 0 to K (N = K + 6
vertices). By Lemma 11 a valid gadget needs a size-3 or a free orbit, so the
default run visits only the compositions that have one; it takes seconds.
`--all` does not use the lemma and enumerates every orbit composition. This
is the enumeration reported in the paper; it is long, because the composition
of six fixed vertices alone has 2^39 candidates.

## The candidates

A candidate (Definition 1) has the literals x0 x1 x2 (vertices 0 1 2), the
palette anchors G_T G_F G_B (3 4 5), and k = N - 6 auxiliary vertices (6, 7,
...). Under the S3 action the auxiliary vertices form orbits of size 1, 2, 3
or 6 (Lemma 6); the list of sizes is an *orbit composition*, e.g. `[3, 3]`
for the trident.

| pairs | |
|---|---|
| palette triangle, x_i -- G_B | always present |
| literal -- literal | never present (Definition 1) |
| literal -- G_T, literal -- G_F | never present: such an edge rejects a satisfying input (note in the proof of Lemma 11) |
| every pair with an auxiliary endpoint | free: binom(k,2) + 6k pairs |

Pairs in the same S3-orbit are present or absent together, so a candidate is
one Boolean choice per edge orbit (a *switch*). A composition with q
auxiliary orbits has the K structural edge orbits printed beneath its panel
in Fig. 5 and three palette attachments per auxiliary orbit: K + 3q switches,
2^(K+3q) candidates. These are the numbers of the paper: 2^14 for the two
size-3 orbits of the trident, binom(k,2) + 4k switches for k fixed vertices,
and the totals of Table 1 (`--test` prints them).

A candidate is *valid* if, with the anchors colored T, F, B, a proper
3-coloring exists for exactly the satisfying inputs. For a symmetric
candidate the eight inputs collapse to four classes: FFF, TFF, TTF, TTT.

## The search

- Within each k, the compositions run in ascending order of their number of
  switches: the compositions with the largest orbits come first.
- The switches are decided one by one. Adding edges can only destroy
  3-colorability, so a subtree is pruned as soon as a satisfiable input is no
  longer colorable. Every line satisfies `leaves + pruned = candidates`; the
  program stops with an error otherwise.
- The settings of the first ten switches are dealt out to 16 threads. The
  result does not depend on the number of cores.
- Each valid gadget is printed (edges other than the fixed ones) and compared
  with the trident of Fig. 2(c).

## Results

Lean 4.33.0. The full output is in `logs/`.

`lake exe sweep --max=6` (`logs/sweep.log`; Apple M1 Max, about two seconds):

| composition | K | candidates | valid |
|---|---|---|---|
| `[3]` | 3 | 2^6 | 0 |
| `[1, 3]` | 5 | 2^11 | 0 |
| `[2, 3]` | 6 | 2^12 | 0 |
| `[1, 1, 3]` | 8 | 2^17 | 0 |
| `[6]` | 7 | 2^10 | 0 |
| `[3, 3]` | 8 | 2^14 | 2 |
| `[1, 2, 3]` | 9 | 2^18 | 0 |
| `[1, 1, 1, 3]` | 12 | 2^24 | 0 |

The two valid gadgets of `[3, 3]` are the trident with either of its two
size-3 orbits as the branch layer.

`lake exe sweep --max=6 --all` (`logs/sweep-all.log`; AMD Ryzen 5 2600, 12
threads, 5 h 32 min): all 24 orbit compositions with N <= 12. The result is
the same: two valid gadgets, both on `[3, 3]`, both the trident. The 16
compositions that have neither a size-3 nor a free orbit contain no valid
gadget, as Lemma 11 states. The three largest:

| composition | K | candidates | leaves | valid | time |
|---|---|---|---|---|---|
| `[1, 1, 1, 1, 1]` | 15 | 2^30 | 49,987,943 | 0 | 90 s |
| `[1, 1, 1, 1, 2]` | 16 | 2^31 | 58,643,092 | 0 | 133 s |
| `[1, 1, 1, 1, 1, 1]` | 21 | 2^39 | 9,023,791,282 | 0 | 5 h 28 min |

`lake exe sweep --test` (`logs/test.log`): binom(k,2) + 6k free pairs and
binom(k,2) + 4k switches for k fixed vertices; Table 1 (2^30, 2^40, 2^51,
2^63 unconstrained; about 2^22, 2^30, 2^39, 2^49 S3-symmetric); the trident,
the Kleinberg-Tardos gadget and the OR-chain are valid, and the
Sharma-Chaudhari gadget rejects (T,T,T).

## Lean 4 proof of minimality and uniqueness

We found the trident with the enumeration above, which uses Lean as a
programming language to search concrete candidates. That search is what
the paper reports. Building on it, we then completed a formal verification
with the Lean theorem prover, after the paper was submitted.

The folder [`with-lean4-complete-proof/`](with-lean4-complete-proof/) is a
separate Lean 4 project with Mathlib. It is a machine-checked proof that the
trident is the minimum S3-symmetric clause gadget.
- The search is proved sound and complete.
- At build time it proves that no S3-symmetric gadget exists with N ≤ 9.
- At build time it also proves that in `[3, 3]` (N = 12) the only valid
  gadget is the trident.

The remaining compositions up to N = 12 are covered by a run of its verified
search. See its README for the theorems, the trusted base and the build.

## Provenance

The code was written by Claude (Anthropic) from the definitions in the paper
and from the authors' original enumeration program, of which it is a shorter
re-implementation. Both programs were run on the compositions `[3]`,
`[1, 3]`, `[2, 3]`, `[1, 1, 3]`, `[6]` and `[3, 3]`: they report the same
valid gadgets, and the original counts four times as many candidates because
it also switches the literal -- G_T and literal -- G_F pairs, which are
excluded here.

## Contact

Minkyoung Cho, mkcho@mju.ac.kr (or minkcho@gmail.com).

## License

MIT. See `LICENSE`.
