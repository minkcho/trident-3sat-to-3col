import atlas.ProofsSym
import atlas.ProofsOrbit
import atlas.Gadgets
/-!
  P5: the decide endpoints.

  The negative and uniqueness claims so far had the shape "theorem plus
  one run of the sweep" (P3/P4), with the run either external or -- for
  raw minimality -- a `native_decide` that adds the compiler to the
  trusted base. This file closes the loop inside the build: the sweep
  premises are re-run at build time -- by kernel `decide` (`decide
  +kernel`, standard axioms only) wherever the slice is small enough,
  by `native_decide` for the two large slices (trust note below) -- so
  the statements below are self-contained theorems with no external
  execution.

  Contents: the two directions of the walk/`gadgetK` bridge in positive
  form (`found_gadgetK_threeColoring`, `gadgetK_mem_found_threeColoring`),
  re-runs of the symmetric sweeps for every slice with at most 3
  auxiliary vertices (six in the kernel, [1, 1, 1] by `native_decide`;
  [opus5.5 review] was "kernel re-runs"), the headline emptiness theorem
  (`no_small_symmetric_gadget_threeColoring` -- judged by the raw
  eight-row table, via P4), and the trident-slice uniqueness endpoint
  (`trident_unique_threeColoring`): the [3, 3] slice contains exactly
  the two tridents.

  Trust note: the bridge, the headline arguments, and six of the eight
  slice re-runs (up to 2^12 candidates; [opus5.5 review] was "seven": the
  seven k <= 3 slices plus the trident slice) are kernel `decide` -- standard
  axioms, no compiler. The two large re-runs -- `sym_empty_111` (2^17)
  and `trident_slice_found` (2^16) -- are `native_decide`: on sweeps
  beyond roughly 2^13 candidates the kernel evaluator's memory use is
  pathological (measured >13-20 GB, thrashing, hours) where the
  compiled run takes seconds. Those two premises trust the compiler --
  the same trust class as the raw minimality re-runs in
  `ProofsRawMin`; the measured ~2^12-13 boundary is the practical
  limit of pure-kernel decide endpoints on this engine.
-/

namespace Atlas

open List

-- ------------------------------ the walk bridge, positive membership form

/-- Soundness of the found list, `gadgetK` form: every reported entry is
    a valid gadget with the reported budget. -/
theorem found_gadgetK_threeColoring (parts : List Nat) (symmetry : Bool)
    {g : List Edge} {k : Nat}
    (h : (g, k) ∈ (searchSlice threeColoring parts symmetry).2.found) :
    gadgetK threeColoring parts g symmetry = some k := by
  have hfound : (searchSlice threeColoring parts symmetry).2.found
      = ((searchAux threeColoring (threeColoring.attach parts).1
          (anchorsOf parts.length (threeColoring.attach parts).1)
          (gadgetRows threeColoring symmetry)
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).2
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).1
          { total := 2 ^ ((threeColoring.attach parts).1.splitForced
              (threeColoring.attach parts).2 symmetry).2.length }).found).reverse := by
    rfl
  rw [hfound] at h
  have hmem := List.mem_reverse.mp h
  rcases searchAux_sound threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry) _ _ _ (g, k) hmem with h0 | hchk
  · cases h0
  · rw [gadgetK_3col_eq]
    exact hchk

/-- Completeness of the found list, `gadgetK` form: a passing graph of
    the slice puts its walk representative (a permutation of it) in the
    found list. -/
theorem gadgetK_mem_found_threeColoring (parts : List Nat) (symmetry : Bool)
    (mask k : Nat)
    (hg : gadgetK threeColoring parts
        (graphAt ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).1
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).2 mask) symmetry
      = some k) :
    (walkGraph ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 mask
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1, k)
      ∈ (searchSlice threeColoring parts symmetry).2.found := by
  rw [gadgetK_3col_eq] at hg
  have hperm := walkGraph_perm_graphAt
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).1
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).2 mask
  have hchk : checkGadget threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry)
      (walkGraph ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 mask
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1) = some k := by
    rw [checkGadget_perm_3col _ _ _ hperm]
    exact hg
  have hmem := searchAux_complete threeColoring (threeColoring.attach parts).1
    (anchorsOf parts.length (threeColoring.attach parts).1)
    (gadgetRows threeColoring symmetry)
    (threeColoring_kill _ _ _)
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).2
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).1
    { total := 2 ^ ((threeColoring.attach parts).1.splitForced
        (threeColoring.attach parts).2 symmetry).2.length }
    mask k hchk
  have hfound : (searchSlice threeColoring parts symmetry).2.found
      = ((searchAux threeColoring (threeColoring.attach parts).1
          (anchorsOf parts.length (threeColoring.attach parts).1)
          (gadgetRows threeColoring symmetry)
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).2
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).1
          { total := 2 ^ ((threeColoring.attach parts).1.splitForced
              (threeColoring.attach parts).2 symmetry).2.length }).found).reverse := by
    rfl
  rw [hfound]
  exact List.mem_reverse.mpr hmem

-- ---- the symmetric sweeps at k <= 3 (six in the kernel, [1,1,1] native)
-- [opus5.5 review] header was "inside the kernel"

theorem sym_empty_nil : (searchSlice threeColoring [] true).2.found = [] := by
  decide +kernel

theorem sym_empty_1 : (searchSlice threeColoring [1] true).2.found = [] := by
  decide +kernel

theorem sym_empty_2 : (searchSlice threeColoring [2] true).2.found = [] := by
  decide +kernel

theorem sym_empty_3 : (searchSlice threeColoring [3] true).2.found = [] := by
  decide +kernel

theorem sym_empty_11 : (searchSlice threeColoring [1, 1] true).2.found = [] := by
  decide +kernel

theorem sym_empty_12 : (searchSlice threeColoring [1, 2] true).2.found = [] := by
  decide +kernel

/-- The one large slice at k ≤ 3 (2^17): `native_decide` -- see the
    trust note in the module docstring. -/
theorem sym_empty_111 :
    (searchSlice threeColoring [1, 1, 1] true).2.found = [] := by
  native_decide

/-- P5 emptiness headline: every slice of the symmetric atlas with at
    most 3 auxiliary vertices contains no 3-coloring clause gadget
    (among the enumerated candidates over the palette framework) --
    judged by the raw eight-row table (P4 lifts the four-class sweeps).
    Axioms: the standard three plus the compiler trust of the single
    `native_decide` premise `sym_empty_111`; the six other slice
    re-runs are kernel `decide`. For every S3-invariant graph, not only
    the enumerated list, see `no_small_symmetric_gadget_threeColoring_invariant`
    (ProofsCover.lean). -/
theorem no_small_symmetric_gadget_threeColoring :
    ∀ k, k ≤ 3 → ∀ parts ∈ compositions k [1, 2, 3, 6],
      ∀ g ∈ (threeColoring.attach parts).1.graphs (symmetry := true)
          (forced := (threeColoring.attach parts).2),
        gadgetK threeColoring parts g false = none := by
  intro k hk
  interval_cases k <;> intro parts hparts
  · have hc : compositions 0 [1, 2, 3, 6] = [[]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    rcases List.mem_cons.mp hparts with rfl | h
    · exact searchSlice_symmetric_covers_raw [] (by decide) sym_empty_nil
    · exact absurd h List.not_mem_nil
  · have hc : compositions 1 [1, 2, 3, 6] = [[1]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    rcases List.mem_cons.mp hparts with rfl | h
    · exact searchSlice_symmetric_covers_raw [1] (by decide) sym_empty_1
    · exact absurd h List.not_mem_nil
  · have hc : compositions 2 [1, 2, 3, 6] = [[1, 1], [2]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    rcases List.mem_cons.mp hparts with rfl | hparts
    · exact searchSlice_symmetric_covers_raw [1, 1] (by decide) sym_empty_11
    rcases List.mem_cons.mp hparts with rfl | h
    · exact searchSlice_symmetric_covers_raw [2] (by decide) sym_empty_2
    · exact absurd h List.not_mem_nil
  · have hc : compositions 3 [1, 2, 3, 6] = [[1, 1, 1], [1, 2], [3]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    rcases List.mem_cons.mp hparts with rfl | hparts
    · exact searchSlice_symmetric_covers_raw [1, 1, 1] (by decide) sym_empty_111
    rcases List.mem_cons.mp hparts with rfl | hparts
    · exact searchSlice_symmetric_covers_raw [1, 2] (by decide) sym_empty_12
    rcases List.mem_cons.mp hparts with rfl | h
    · exact searchSlice_symmetric_covers_raw [3] (by decide) sym_empty_3
    · exact absurd h List.not_mem_nil

-- ---- the trident slice (native re-run; the two tridents' checks in the kernel)
-- [opus5.5 review] header was "inside the kernel"

/-- First find of the [3, 3] sweep, in walk order: the trident with the
    literal layer on part 0 (lits -> layer 0 -> layer 1 triangle). -/
def tridentA : List Edge :=
  [(.aux 1 0, .aux 1 1), (.aux 1 0, .aux 1 2), (.aux 1 1, .aux 1 2),
   (.aux 0 0, .aux 2 0), (.aux 0 1, .aux 2 0), (.aux 0 2, .aux 2 0),
   (.aux 0 0, .aux 1 0), (.aux 0 1, .aux 1 1), (.aux 0 2, .aux 1 2),
   (.lit 0, .aux 0 0), (.lit 1, .aux 0 1), (.lit 2, .aux 0 2),
   (.lit 0, .aux 4 0), (.lit 1, .aux 4 0), (.lit 2, .aux 4 0),
   (.aux 2 0, .aux 3 0), (.aux 2 0, .aux 4 0), (.aux 3 0, .aux 4 0)]

/-- Second find of the [3, 3] sweep: the same trident with the two
    layers' roles swapped (lits -> layer 1 -> layer 0 triangle). -/
def tridentB : List Edge :=
  [(.aux 1 0, .aux 2 0), (.aux 1 1, .aux 2 0), (.aux 1 2, .aux 2 0),
   (.aux 0 0, .aux 1 0), (.aux 0 1, .aux 1 1), (.aux 0 2, .aux 1 2),
   (.aux 0 0, .aux 0 1), (.aux 0 0, .aux 0 2), (.aux 0 1, .aux 0 2),
   (.lit 0, .aux 1 0), (.lit 1, .aux 1 1), (.lit 2, .aux 1 2),
   (.lit 0, .aux 4 0), (.lit 1, .aux 4 0), (.lit 2, .aux 4 0),
   (.aux 2 0, .aux 3 0), (.aux 2 0, .aux 4 0), (.aux 3 0, .aux 4 0)]

/-- The build-time re-run of the trident slice: the sweep finds exactly
    the two tridents, both with budget 1. `native_decide` -- see the
    trust note in the module docstring. -/
theorem trident_slice_found :
    (searchSlice threeColoring [3, 3] true).2.found
      = [(tridentA, 1), (tridentB, 1)] := by
  native_decide

/-- The two finds are the named trident, in its two layer orders. -/
theorem tridentA_perm : tridentA.Perm (tridentGraph 0 1 2 3 4) := by
  decide

theorem tridentB_perm : tridentB.Perm (tridentGraph 1 0 2 3 4) := by
  decide

/-- The positive direction: both finds are valid gadgets with budget 1.
    Single-graph checks, so plain kernel `decide` (standard axioms) rather
    than a detour through the `native_decide` slice re-run. -/
theorem tridentA_gadgetK : gadgetK threeColoring [3, 3] tridentA true = some 1 := by
  decide

theorem tridentB_gadgetK : gadgetK threeColoring [3, 3] tridentB true = some 1 := by
  decide

/-- P5 uniqueness headline: in the trident slice, every valid gadget
    has budget 1 and its edge set is one of the two tridents. Axioms:
    the standard three plus the compiler trust of the `native_decide`
    premise `trident_slice_found` (the bridge and the argument are
    kernel-checked). For every S3-invariant graph see
    `trident_unique_threeColoring_invariant` (ProofsCover.lean). -/
theorem trident_unique_threeColoring :
    ∀ g ∈ (threeColoring.attach [3, 3]).1.graphs (symmetry := true)
        (forced := (threeColoring.attach [3, 3]).2),
      ∀ k, gadgetK threeColoring [3, 3] g true = some k →
        k = 1 ∧ (g.Perm tridentA ∨ g.Perm tridentB) := by
  intro g hg k hk
  unfold Universe.graphs at hg
  obtain ⟨mask, _, rfl⟩ := List.mem_map.mp hg
  have hmem := gadgetK_mem_found_threeColoring [3, 3] true mask k hk
  rw [trident_slice_found] at hmem
  have hperm := walkGraph_perm_graphAt
    ((threeColoring.attach [3, 3]).1.splitForced
      (threeColoring.attach [3, 3]).2 true).1
    ((threeColoring.attach [3, 3]).1.splitForced
      (threeColoring.attach [3, 3]).2 true).2 mask
  rcases List.mem_cons.mp hmem with heq | hmem'
  · injection heq with h1 h2
    exact ⟨h2, Or.inl (h1 ▸ hperm.symm)⟩
  rcases List.mem_cons.mp hmem' with heq | h
  · injection heq with h1 h2
    exact ⟨h2, Or.inr (h1 ▸ hperm.symm)⟩
  · exact absurd h List.not_mem_nil

/-- The uniqueness endpoint against the raw eight-row table, via the P4
    symmetry reduction: same slice, same two tridents. -/
theorem trident_unique_threeColoring_raw :
    ∀ g ∈ (threeColoring.attach [3, 3]).1.graphs (symmetry := true)
        (forced := (threeColoring.attach [3, 3]).2),
      ∀ k, gadgetK threeColoring [3, 3] g false = some k →
        k = 1 ∧ (g.Perm tridentA ∨ g.Perm tridentB) := by
  intro g hg k hk
  obtain ⟨hsub, hcl⟩ := graphs_symmetric_props
    (attach_legal [3, 3] (by decide)) rfl (threeColoring.attach [3, 3]).2 g hg
  rw [← gadgetK_s3_symmetry_reduction_threeColoring [3, 3] (by decide) hsub hcl] at hk
  exact trident_unique_threeColoring g hg k hk

end Atlas
