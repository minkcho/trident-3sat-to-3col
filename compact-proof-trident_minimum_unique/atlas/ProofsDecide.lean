import atlas.ProofsSym
import atlas.ProofsOrbit
/-!
  The decide endpoints used by Theorem 16.

  * `gadgetK_mem_found_threeColoring`: a graph of a slice that passes
    `gadgetK` puts its walk representative into the found list of the sweep.
  * `sym_empty_3`: the symmetric sweep of the slice [3] finds nothing,
    re-run by kernel `decide` (standard axioms only).
  * `trident_slice_found`: the sweep of the trident slice [3, 3] finds
    exactly the two tridents `tridentA` and `tridentB`, both with budget 1.
    This re-run (2^16 candidates) is `native_decide` and trusts the
    compiler: on sweeps beyond about 2^13 candidates the kernel evaluator's
    memory use is impractical (measured above 13 GB) where the compiled run
    takes seconds.
  * `trident_unique_threeColoring` / `_raw`: in the trident slice, every
    valid gadget has budget 1 and the edge set of one of the two tridents,
    against the four-class table and against the raw eight-row table.
-/

namespace Atlas

open List

-- ------------------------------ the walk bridge, positive membership form

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

-- ---- the symmetric sweep of [3] (kernel)

theorem sym_empty_3 : (searchSlice threeColoring [3] true).2.found = [] := by
  decide +kernel

-- ---- the trident slice (native re-run)

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
