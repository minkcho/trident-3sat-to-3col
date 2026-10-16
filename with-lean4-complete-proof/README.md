# Lean 4 proof: the trident as the minimum S3-symmetric clause gadget

A machine-checked proof, in Lean 4 with Mathlib, of the minimality and
uniqueness of the trident among S3-symmetric clause gadgets for the
reduction from 3SAT to 3-coloring, together with a verified search for the
cases that are not re-run at build time.

## Background

We first found the symmetric gadget with Lean used as a programming
language. An executable search over concrete candidate gadgets, the
enumeration in the parent folder, returned the trident. Building on that
result, we used the Lean theorem prover to complete the formal
verification in this folder. The verification came after the paper was
submitted, so the paper reports only the enumeration.

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

**At build time.** These are theorems, checked whenever the project is
built.
- `no_small_symmetric_gadget_threeColoring_invariant`: no S3-symmetric
  candidate with N ≤ 9 vertices (at most three auxiliary vertices) is a
  valid clause gadget.
- `trident_unique_threeColoring_invariant`: every valid S3-symmetric
  candidate of composition `[3, 3]` (N = 12) is the trident, with either
  size-3 orbit as the branch layer. `trident_slice_found` shows that both
  labelings are found, with budget 1.

The `_invariant` forms hold for every S3-invariant graph on these vertices,
not only for the enumerated list.

**By a certified run.** The remaining cases are not re-run at build time:
N = 10 and 11, and the other compositions at N = 12.
`lake exe atlas-sweep three_coloring --max=6 --require-layer` enumerates the
compositions with a size-3 or size-6 orbit. The paper shows that the other
compositions carry no valid gadget.

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
`Quot.sound`) plus two `native_decide` re-runs of the search, which trust
the compiled code. Both are in `ProofsDecide.lean`:
- `trident_slice_found`: the `[3, 3]` slice, 2^16 candidates;
- `sym_empty_111`: the symmetric `[1, 1, 1]` slice, 2^17 candidates.

The other small slices are re-run by kernel `decide`. Lean 4.33 reports each
`native_decide` as an auxiliary axiom `<theorem>._native.native_decide.ax_1_1`.

A census of all 499 theorems with `#print axioms` gives:
- 492 use only the standard axioms;
- 7 depend on one of the two re-runs: the two themselves,
  `no_small_symmetric_gadget_threeColoring` (and `_invariant`) and
  `trident_unique_threeColoring` (and `_invariant`, `_raw`);
- none uses `sorry`.

The search-correctness theorems use only the standard axioms.

## Build

```bash
lake exe cache get     # Mathlib build cache for the pinned version (network, several GB under .lake/)
lake build             # type-checking the proofs is the verification
lake exe atlas-sweep three_coloring --max=6 --require-layer   # the certified run
```

Measured on 2026-10-16 on an Intel Core i7-8700 (12 threads) with Lean
4.33.0:

| command | time |
|---|---|
| `lake exe cache get` | about 1.3 min |
| `lake build` (1,108 jobs) | 2 min 25 s, of which `ProofsDecide` (the build-time re-runs) takes 136 s |

The build reports no errors and no warnings.

## Files

| file | role |
|---|---|
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

The files come unchanged from the authors' larger framework, which covers
several graph problems and the full reduction. Only the files needed here
were kept, so some comments still refer to the larger framework:
- "the full line", "atlas-ext2", "P1" to "P8" and "round" refer to it and
  its development rounds.
- Comments tagged `[opus5.5 review]` record documentation corrections from
  a review pass on 2026-09-23.

None of this affects the definitions or the proofs.

## License

MIT. See `../LICENSE`.
