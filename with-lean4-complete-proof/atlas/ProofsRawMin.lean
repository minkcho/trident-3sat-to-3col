import Mathlib.Tactic.IntervalCases
import atlas.ProofsWalkBridge
/-!
  The raw-minimality proposition for 3-coloring, as a single theorem:
  the raw (symmetry-free) spaces with at most 3 auxiliary vertices
  contain no valid clause gadget, and the space with 4 does.

  The emptiness side is `searchSlice_exhaustive_threeColoring_graphs`
  (P3) applied to re-runs of the plain raw walk (`searchSlice … false`; the
  sweep's default raw mode is the orderly walk -- [opus5.5 review]) — the k=3 instance walks all
  2^27 candidate graphs (with the pruning P2/P3 proved lossless) at
  build time. The existence side is a concrete 15-edge witness from the
  sweep's 30 finds (class-3 representative).

  Trust note (P5 update; witness purified 2026-09-02): the k=0 and k=1
  re-runs (2^6 and 2^12) and the single-graph witness check are kernel
  `decide` — standard axioms only. Only the k=2 and k=3 re-runs (2^19
  and 2^27) use `native_decide`, which extends the trusted base with
  the Lean compiler (`Lean.ofReduceBool`). The only other `native_decide` sites of the
  project are the two large slice re-runs of `ProofsDecide`
  (`sym_empty_111`, `trident_slice_found`); every theorem that does not
  depend on these four premises uses only the standard axioms.

  [opus5.5 review, axiom census 2026-09-23] Under Lean 4.33 each use shows
  up in `#print axioms` as an auxiliary axiom
  `<theorem>._native.native_decide.ax_1_1` (asserting the compiled
  `decide … = true`), not as `Lean.ofReduceBool`. Of the 1,356 atlas
  theorems, 10 depend on one: the four re-runs and
  `raw_minimality_threeColoring`, `no_small_symmetric_gadget_threeColoring`
  (+ `_invariant`) and `trident_unique_threeColoring` (+ `_invariant`,
  `_raw`); the other 1,346 use a subset of the standard three.
-/

namespace Atlas

open List

/-- Class-3 representative of the 30 raw aux=4 finds (g6 of the sweep):
    parts `[1,1,1,1]`, palette parts 4-6 appended by `attach`. -/
def rawWitness : List Edge :=
  [(.aux 0 0, .aux 1 0), (.aux 0 0, .aux 2 0), (.aux 1 0, .aux 3 0),
   (.aux 2 0, .aux 4 0), (.aux 3 0, .aux 4 0), (.aux 4 0, .aux 5 0),
   (.aux 4 0, .aux 6 0), (.aux 5 0, .aux 6 0),
   (.lit 0, .aux 0 0), (.lit 0, .aux 2 0), (.lit 0, .aux 6 0),
   (.lit 1, .aux 1 0), (.lit 1, .aux 6 0),
   (.lit 2, .aux 3 0), (.lit 2, .aux 6 0)]

theorem raw_empty_0 :
    ((searchSlice threeColoring (List.replicate 0 1) false).2.found).isEmpty = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem raw_empty_1 :
    ((searchSlice threeColoring (List.replicate 1 1) false).2.found).isEmpty = true := by
  decide +kernel

theorem raw_empty_2 :
    ((searchSlice threeColoring (List.replicate 2 1) false).2.found).isEmpty = true := by
  native_decide

theorem raw_empty_3 :
    ((searchSlice threeColoring (List.replicate 3 1) false).2.found).isEmpty = true := by
  native_decide

theorem raw_exists_4 :
    gadgetK threeColoring [1, 1, 1, 1] rawWitness false = some 1 := by
  decide

/-- Raw minimality: no valid 3-coloring clause gadget exists with at
    most 3 auxiliary vertices, and one exists with 4 -- among the enumerated
    raw candidates over the palette framework (palette triangle and `G_B`
    fan forced, no literal-literal edges; [opus5.5 review] scope stated).
    Axioms: the standard three plus the `native_decide` premises
    `raw_empty_2`, `raw_empty_3`. -/
theorem raw_minimality_threeColoring :
    (∀ k, k ≤ 3 →
      ∀ g ∈ (threeColoring.attach (List.replicate k 1)).1.graphs
          (symmetry := false)
          (forced := (threeColoring.attach (List.replicate k 1)).2),
        gadgetK threeColoring (List.replicate k 1) g false = none) ∧
    gadgetK threeColoring [1, 1, 1, 1] rawWitness false = some 1 := by
  refine ⟨?_, raw_exists_4⟩
  intro k hk
  interval_cases k
  · exact searchSlice_exhaustive_threeColoring_graphs _ false
      (List.isEmpty_iff.mp raw_empty_0)
  · exact searchSlice_exhaustive_threeColoring_graphs _ false
      (List.isEmpty_iff.mp raw_empty_1)
  · exact searchSlice_exhaustive_threeColoring_graphs _ false
      (List.isEmpty_iff.mp raw_empty_2)
  · exact searchSlice_exhaustive_threeColoring_graphs _ false
      (List.isEmpty_iff.mp raw_empty_3)

end Atlas
