# with-lean4-complete-proof

A machine-checked proof, in Lean 4 with Mathlib, behind the enumeration in
the parent folder and behind the trident reduction itself.

The parent folder (`../Color.lean`, `../Sweep.lean`) holds the standalone,
dependency-free enumeration quoted in the paper. This folder is a separate
Lean project. It re-implements the gadget search inside a general framework
for clause-gadget search ("atlas"), proves the search correct, re-runs the
small slices and the trident slice at build time, and proves that the
reduction is correct for every formula.

## What is proved

**The search is correct (L1, L2).** The following are proved, so a run of
`lake exe atlas-sweep` is a certified enumeration.
- The 3-coloring check decides whether a proper 3-coloring extends the
  pinned colors.
- Pruning loses no gadget.
- The walk visits every candidate of a slice, with or without the S3
  reduction.

The run itself is executed by compiled code, as in the parent folder.

**Build-time results (L2).** The `_invariant` forms hold for every
S3-invariant graph, not only for the enumerated list.
- `no_small_symmetric_gadget_threeColoring` (and `_invariant`): no
  S3-symmetric candidate with at most three auxiliary vertices (N ≤ 9) is a
  valid clause gadget.
- `trident_unique_threeColoring` (and `_invariant`, `_raw`): in the
  composition `[3, 3]` (N = 12), every valid gadget has budget 1 and is one
  of the two tridents, i.e. the trident with either size-3 orbit as the
  branch layer.
- `raw_minimality_threeColoring`: without symmetry, no valid gadget exists
  with at most three auxiliary vertices, and one exists with four.

The other symmetric compositions with N = 10, 11, 12 are not re-run at build
time. They rest on the verified search together with a run.
`lake exe atlas-sweep three_coloring --max=6 --require-layer` visits the
compositions with a size-3 or size-6 orbit. The paper shows that the
remaining compositions carry no valid gadget, and the parent folder's
`--all` run checks them directly.

**The reduction (L3).** For every well-formed formula, the graph assembled
from trident copies on a shared literal layer is 3-colorable with only the
palette pinned iff the formula is satisfiable. Well-formed means every clause
has exactly three literals over pairwise-distinct variables.
- `trident_colorable_iff`: the pin-free statement, i.e. the reduction itself.
- `trident_multiK_iff`: the table-level statement. The multi-clause table
  reads budget 1 iff the formula is satisfiable.

## The chain, file by file

| rung | what is proved | where |
|---|---|---|
| L1 verifier | `colorable` (the backtracker) decides "a proper 3-coloring extends the pins" | `ProofsColorK.lean` (palette-generic kernel), `ProofsColor.lean:colorable_iff_spec` |
| L1 pruning | the viable bound is antitone in the edge set, so pruning loses no gadget | `ProofsPrune.lean:colorable_antitone, colorsOk_antitone` |
| L2 walk | the pruned walk is sound and complete for a slice | `ProofsWalk.lean:searchAux_sound/_complete`, `ProofsWalkBridge.lean:searchSlice_exhaustive_threeColoring_graphs` |
| L2 symmetry | the four-class table equals the eight-row table on symmetric candidates | `ProofsSym.lean:gadgetK_s3_symmetry_reduction(_threeColoring)` |
| L2 uniqueness / minimality | the trident is the unique `[3, 3]` find; no smaller symmetric gadget; raw minimality; the canonical raw walk is complete | `ProofsDecide.lean`, `ProofsCover.lean`, `ProofsRawMin.lean`, `ProofsRawWalk.lean`, `ProofsShard.lean` |
| L3 table level | for every well-formed formula, the multi-clause table reads 1 iff the formula is satisfiable | `ProofsMultiCol.lean:multiK_threeColoring_iff, trident_multiK_iff` |
| L3 pin-free | the assembly is 3-colorable with only the palette pinned iff the formula is satisfiable: the reduction itself | `ProofsMultiColFree.lean:layer_forces, colorable_assembly_iff_sat, trident_colorable_iff` |

Support:
- `Atlas.lean`: group, orbits, generation.
- `Framework.lean`: problem interface, budgets, hunts, multi-clause assembly.
- `Kits.lean`: the `feasibility` kit and the mask enumeration.
- `Assemble2.lean`: the generalized assembler that the interface theorems are stated on.
- `Proofs.lean`: compositions and slices.
- Also `ProofsAssemble*.lean`, `ProofsMulti.lean`, `ProofsGlue.lean`, `ProofsAction.lean`, `ProofsOrbit.lean`, `ProofsLib.lean`, `ProofsKits.lean`, `Audit.lean`, `SliceOrder.lean` and `Report.lean`.

## Trusted base

The proofs use the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) plus four `native_decide` re-runs of the search, which trust
the compiled code:

- `trident_slice_found` (the `[3, 3]` slice, 2^16 candidates) and
  `sym_empty_111` (the symmetric `[1, 1, 1]` slice, 2^17), in
  `ProofsDecide.lean`;
- `raw_empty_2` and `raw_empty_3` (raw k = 2 and 3, 2^19 and 2^27), in
  `ProofsRawMin.lean`.

The other slice re-runs are kernel `decide`. Lean 4.33 reports each
`native_decide` as an auxiliary axiom `<theorem>._native.native_decide.ax_1_1`.

A census of all 815 theorems with `#print axioms` gives:

- 805 use only the standard axioms;
- 10 depend on one of the four re-runs: the four themselves,
  `no_small_symmetric_gadget_threeColoring` (and `_invariant`),
  `trident_unique_threeColoring` (and `_invariant`, `_raw`) and
  `raw_minimality_threeColoring`;
- none uses `sorry`.

The reduction theorems use only the standard axioms: `trident_colorable_iff`,
`colorable_assembly_iff_sat`, `trident_multiK_iff`, `multiK_threeColoring_iff`
and `layer_forces`. So do the search-correctness theorems.

## Build

```bash
lake exe cache get     # Mathlib build cache for the pinned version (network, several GB under .lake/)
lake build             # type-checking the proofs is the verification
lake exe atlas-tests   # engine, framework and 3-coloring tests
lake exe atlas-demo    # the enumeration census, the [3, 3] hunt, the micro-universe check
lake exe atlas-sweep three_coloring --max=6 --require-layer   # the exhaustive sweep
```

Measured on 2026-10-16 on an Intel Core i7-8700 (12 threads) with Lean
4.33.0:

| command | time |
|---|---|
| `lake exe cache get` | about 1.5 min |
| `lake build` (1,134 jobs) | 18 min 50 s, of which `ProofsRawMin` (the 2^27 raw re-run) takes 1,123 s and `ProofsDecide` 139 s |
| `lake exe atlas-tests` | 25 s, all tests passed |
| `lake exe atlas-demo` | 3 s |

The build reports no errors and no warnings. The sweep was not timed here.

## Notes on the sources

This folder is the 3-coloring part of the authors' larger framework, which
covers several graph problems. The definitions and proofs are those of the
larger framework, with only the other problems removed, so some comments
still refer to it:
- "the full line" and "atlas-ext2" mean the larger framework.
- "P1" to "P8", "round" and "review" refer to its development rounds.
- Comments tagged `[opus5.5 review]` record documentation corrections from
  a review pass on 2026-09-23.

None of this affects the definitions or the proofs.

## License

MIT. See `../LICENSE`.
