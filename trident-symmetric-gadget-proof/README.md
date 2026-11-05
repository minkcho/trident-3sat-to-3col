# Lean 4 proof: the trident as the minimum S3-symmetric clause gadget

A machine-checked proof, in Lean 4 with Mathlib, of Theorem 16 of the paper
for candidates with at most twelve vertices: among the S3-symmetric clause
gadgets for the reduction from 3SAT to 3-coloring, none has fewer than six
auxiliary vertices, and with six the only one is the trident. The candidates
carry the standard S3 action on each orbit; that every gadget of the paper's
Definition 1 has this form is the paper's Lemma 6, which is not formalized.

## Background

We first found the symmetric gadget with Lean used as a programming
language. An executable search over concrete candidate gadgets, the
enumeration in the parent folder, returned the trident. Building on that
result, we used the Lean theorem prover to complete the formal
verification in this folder by Claude (under evaluation by Human). The
verification came after the paper was submitted, so the paper reports only
the enumeration.

## For reviewers

You do not need to read the proofs, because Lean checks them. What needs
checking is that the statements say what the paper claims.

1. Read [`atlas/Statement.lean`](atlas/Statement.lean), 77 lines. It
   gives the four results in one place:
   - the trident is an S3-symmetric candidate;
   - the trident is a valid clause gadget, on all eight inputs;
   - no valid S3-symmetric gadget exists with N ≤ 11 (at most five auxiliary
     vertices);
   - every valid S3-symmetric gadget with N ≤ 12 has composition `[3, 3]` and
     is the trident, under one of its two labelings.
2. Read the definitions these statements use, 256 lines in five files:

   | file | lines | what |
   |---|---|---|
   | `atlas/Atlas.lean` | 30–103, 151–176 | S3 permutations, vertices, the S3 action, candidate edges, orbit compositions |
   | `atlas/Framework.lean` | 20–39, 50–142 | instances, the problem interface, the eight-row validity check `gadgetK` |
   | `atlas/Kits.lean` | 22–36 | the feasibility kit |
   | `atlas/Problems/ThreeColoring.lean` | 16–58 | the 3-coloring check and the palette |
   | `atlas/ProofsDecide.lean` | 205–223 | the trident under its two labelings (`tridentA`, `tridentB`) |

3. Run `lake exe cache get` and then `lake build`. The build checks every
   proof and prints the axioms of the four statements. The first build takes
   about 9 hours, almost all of it in `ProofsSweeps16` (six `native_decide`
   re-runs on one thread); later builds reuse the result and take seconds.

The remaining lines, about 5,200, are proofs and the sweep executable.

## What is proved

**The search is correct.** The following are proved, so a run of
`lake exe atlas-sweep` is a certified enumeration. The run itself is
executed by compiled code.
- The 3-coloring check decides whether a proper 3-coloring extends the
  pinned colors: `colorable_iff_spec`.
- Pruning loses no gadget: `colorable_antitone`.
- The walk is sound and complete for a slice:
  `searchSlice_exhaustive_threeColoring_graphs`.
- On S3-symmetric candidates, the four-class table equals the eight-row
  table: `gadgetK_s3_symmetry_reduction_threeColoring`.

**Theorem 16, at build time.** `trident_minimum_unique`
(`ProofsTheorem16.lean`): for every k ≤ 6, every orbit composition of k, and
every S3-invariant candidate graph, a valid gadget has composition `[3, 3]`,
budget 1, and the edge set of the trident under one of its two labelings.
`no_symmetric_gadget_below_six` is the case k ≤ 5. `atlas/Statement.lean`
restates both, together with two facts proved by kernel `decide`: the trident
is an S3-symmetric candidate, and it is a valid gadget on all eight inputs.
All 24 compositions with k ≤ 6 are covered:
- sizes 1 and 2 only (16 compositions): `gadgetK_none_of_small_orbits`
  (`ProofsSmallOrbits.lean`), a proof for any number of auxiliary vertices on
  the standard axioms. The even permutation (1,2,0) fixes every vertex of
  these orbits and every anchor, so every neighbor of x2 is a neighbor of x0;
  recoloring x2 turns a coloring for (F,F,T) into one for (F,F,F). This is a
  special case of the paper's Lemma 11.
- a size-3 or size-6 orbit, other than `[3, 3]` (7 compositions): the
  symmetric sweep is re-run at build time and finds nothing (`sym_empty_3`
  by kernel `decide`; `sym_empty_13`, `_23`, `_113`, `_6`, `_123`, `_1113`
  by `native_decide` in `ProofsSweeps16.lean`), and
  `searchSlice_symmetric_covers_invariant` lifts this to every S3-invariant
  graph;
- `[3, 3]`: `trident_unique_threeColoring_invariant` (`ProofsCover.lean`),
  from the re-run `trident_slice_found`, which finds both labelings with
  budget 1.

The older theorem `no_small_symmetric_gadget_threeColoring_invariant`
(N ≤ 9) is kept; Theorem 16 above contains it.

**The same sweep as a program.**
`lake exe atlas-sweep three_coloring --max=6 --require-layer` runs the sweep
of the compositions with a size-3 or size-6 orbit outside the proofs. A run
on 2026-10-16 found exactly two valid gadgets, both in `[3, 3]`: the trident
with either size-3 orbit as the branch layer. The run took 21 min 54 s on
one thread of an Intel Core i7-8700.

| composition | N | candidates | valid |
|---|---|---|---|
| `[3]` | 9 | 2^8 | 0 |
| `[1, 3]` | 10 | 2^13 | 0 |
| `[2, 3]` | 11 | 2^14 | 0 |
| `[1, 1, 3]` | 11 | 2^19 | 0 |
| `[6]` | 12 | 2^12 | 0 |
| `[3, 3]` | 12 | 2^16 | 2 |
| `[1, 2, 3]` | 12 | 2^20 | 0 |
| `[1, 1, 1, 3]` | 12 | 2^26 | 0 |

### Search space

A candidate has the literals x0, x1, x2, the palette anchors G_T, G_F, G_B
and the auxiliary orbits.
- Always present: the palette triangle and the G_B fan.
- Never present: literal–literal edges.
- Switched: every other pair, one switch per S3 edge orbit.

This is the paper's candidate space (Definition 1) plus two more switches:
the literal–G_T and literal–G_F orbits. So the engine searches four times
as many candidates; for example, `[3, 3]` has 2^16 here and 2^14 in the
paper. Because the paper's space is contained in this one, the
non-existence and uniqueness results also hold there.

## Trusted base

The proofs use the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) plus `native_decide` re-runs of the search, which trust the
code that Lean evaluates. Lean 4.33 reports each `native_decide` as an
auxiliary axiom `<theorem>._native.native_decide.ax_1_1`. The four results
of `Statement.lean` (`lake build` prints them):

| statement | axioms |
|---|---|
| `trident_is_symmetric_candidate` | the standard three |
| `trident_is_valid` | `propext` |
| `no_valid_symmetric_gadget_below_12_vertices` | the standard three + 7 re-runs |
| `valid_symmetric_gadget_up_to_12_vertices_is_trident` | the standard three + 7 re-runs |

The seven re-runs are `sym_empty_13`, `_23`, `_113`, `_6`, `_123`, `_1113`
(`ProofsSweeps16.lean`) and `trident_slice_found` (the `[3, 3]` slice,
`ProofsDecide.lean`). The small slices, `[3]` included, are re-run by kernel
`decide`.

A census of all 529 theorems with `#print axioms` (2026-11-05) gives:
- 512 use only the standard axioms;
- 17 depend on a `native_decide` re-run: the eight re-runs (the seven above
  and `sym_empty_111`, used only by the older N ≤ 9 theorem) and the
  theorems built on them;
- none uses `sorry`.

The search-correctness theorems use only the standard axioms. So do the
trident's symmetry and validity, and `gadgetK_none_of_small_orbits`.

## Build

```bash
lake exe cache get     # Mathlib build cache for the pinned version (network, several GB under .lake/)
lake build             # type-checking the proofs is the verification
lake exe atlas-sweep three_coloring --max=6 --require-layer   # the certified run
```

Measured on an Intel Core i7-8700 (12 threads) with Lean 4.33.0:

| command | time |
|---|---|
| `lake exe cache get` | about 1.3 min |
| `lake build`, first time (1,112 jobs) | about 8 h 50 min: `ProofsSweeps16` takes 8 h 48 min (2026-11-05), the rest about 2.5 min, of which `ProofsDecide` takes 136 s (2026-10-16) |
| `lake build`, cached | about 9 s |
| `lake exe atlas-sweep three_coloring --max=6 --require-layer` | 21 min 54 s, of which `[1, 1, 1, 3]` takes 21 min |

`native_decide` evaluates the sweep inside the Lean process on one thread,
which is why `ProofsSweeps16` is much slower than the same sweep in the
compiled `atlas-sweep` executable. The build reports no errors and no
warnings.

## Files

| file | role |
|---|---|
| `Statement.lean` | the four results in one place (start here) |
| `ProofsTheorem16.lean` | Theorem 16 for N ≤ 12: `trident_minimum_unique`, `no_symmetric_gadget_below_six` |
| `ProofsSmallOrbits.lean` | no valid gadget with orbits of sizes 1 and 2 only, any number of them |
| `ProofsSweeps16.lean` | the six build-time re-runs for N = 10 to 12 (`native_decide`) |
| `Atlas.lean` | vertices, the S3 action, edge orbits, candidate graphs, compositions |
| `Framework.lean`, `Kits.lean` | the problem interface, the eight-row and four-class tables (`gadgetK`), the search (`searchSlice`), the mask enumeration |
| `Problems/ThreeColoring.lean`, `Problems/KColoring.lean` | the 3-coloring check and the palette |
| `Gadgets.lean` | the trident (`tridentGraph`) |
| `ProofsColorK.lean`, `ProofsColor.lean`, `ProofsPrune.lean` | the check is correct; pruning is lossless |
| `ProofsWalk.lean`, `ProofsWalkBridge.lean` | the walk is sound and complete |
| `ProofsSym.lean`, `ProofsAction.lean`, `ProofsOrbit.lean`, `Proofs.lean` | symmetry reduction, the group action, orbits, compositions |
| `ProofsDecide.lean` | build-time re-runs: small slices, the `[3, 3]` slice, the uniqueness theorem |
| `ProofsCover.lean` | the results for every S3-invariant graph (`_invariant`) |
| `ProofsKits.lean`, `ProofsLib.lean` | enumeration and list lemmas |
| `Audit.lean` | independently computed expectations for the enumeration, used by `Proofs.lean` and the sweep |
| `Sweep.lean`, `Report.lean`, `SliceOrder.lean` | the `atlas-sweep` executable |

## Notes on the sources

Apart from `Statement.lean` and the three files added on 2026-11-04 for
Theorem 16 (`ProofsTheorem16.lean`, `ProofsSmallOrbits.lean`,
`ProofsSweeps16.lean`), the files come unchanged from the authors' larger
framework, which is not public. Only the files needed here were kept, so
some comments still refer to the larger framework:
- "the full line", "atlas-ext2", "P1" to "P8" and "round" refer to it and
  its development rounds.
- Comments tagged `[opus5.5 review]` record documentation corrections from
  a review pass on 2026-09-23.

None of this affects the definitions or the proofs.

## License

MIT. See `../LICENSE`.
