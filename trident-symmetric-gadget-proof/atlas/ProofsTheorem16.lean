import atlas.ProofsCover
import atlas.ProofsSmallOrbits
import atlas.ProofsSweeps16

/-!
  Theorem 16 of the paper, at build time: among the S3-symmetric candidates
  with at most six auxiliary vertices (N ≤ 12), every valid clause gadget is
  the trident.

  Every orbit composition with at most six auxiliary vertices is covered.
  * Compositions of sizes 1 and 2 only: `gadgetK_none_of_small_orbits`
    (ProofsSmallOrbits), a proof for any number of auxiliary vertices.
  * Compositions with a size-3 or a size-6 orbit other than `[3, 3]`: the
    symmetric sweep is re-run at build time and finds nothing (`sym_empty_3`
    in ProofsDecide and the six re-runs of ProofsSweeps16), and
    `searchSlice_symmetric_covers_invariant` lifts this to every S3-invariant
    graph.
  * `[3, 3]`: `trident_unique_threeColoring_invariant` (ProofsCover).

  The statement is about the formal candidate space: each orbit carries the
  standard action of its size, and orbits are listed in non-decreasing order
  of size. That every S3-symmetric gadget of Definition 1 can be relabeled
  into this form is the paper's Lemma 6, which is not formalized here.
-/

namespace Atlas

/-- Theorem 16 in the formal model (minimality and uniqueness up to twelve
    vertices). -/
theorem trident_minimum_unique :
    ∀ k, k ≤ 6 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      (∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges) →
      (∀ s ∈ perms, ∀ e ∈ g, (threeColoring.attach parts).1.actEdge s e ∈ g) →
      (∀ f ∈ (threeColoring.attach parts).2, normEdge f ∈ g) →
      ∀ b, gadgetK threeColoring parts g false = some b →
        parts = [3, 3] ∧ b = 1 ∧
          ((∀ e, e ∈ g ↔ e ∈ tridentA) ∨ (∀ e, e ∈ g ↔ e ∈ tridentB)) := by
  intro k hk parts hparts g hsub hinv hforced b hb
  -- compositions of sizes 1 and 2 only
  have small : (∀ n ∈ parts, n = 1 ∨ n = 2) → False := fun hs => by
    rw [gadgetK_none_of_small_orbits parts hs hsub hinv] at hb
    cases hb
  -- compositions whose symmetric sweep finds nothing
  have empty : (∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) →
      (searchSlice threeColoring parts true).2.found = [] → False :=
    fun hl hf => by
      rw [searchSlice_symmetric_covers_invariant parts hl hf hsub hinv hforced] at hb
      cases hb
  interval_cases k
  · have hc : compositions 0 [1, 2, 3, 6] = [[]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    subst hparts
    exact (small (by decide)).elim
  · have hc : compositions 1 [1, 2, 3, 6] = [[1]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    subst hparts
    exact (small (by decide)).elim
  · have hc : compositions 2 [1, 2, 3, 6] = [[1, 1], [2]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    rcases hparts with rfl | rfl <;> exact (small (by decide)).elim
  · have hc : compositions 3 [1, 2, 3, 6] = [[1, 1, 1], [1, 2], [3]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    rcases hparts with rfl | rfl | rfl
    · exact (small (by decide)).elim
    · exact (small (by decide)).elim
    · exact (empty (by decide) sym_empty_3).elim
  · have hc : compositions 4 [1, 2, 3, 6]
        = [[1, 1, 1, 1], [1, 1, 2], [1, 3], [2, 2]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    rcases hparts with rfl | rfl | rfl | rfl
    · exact (small (by decide)).elim
    · exact (small (by decide)).elim
    · exact (empty (by decide) sym_empty_13).elim
    · exact (small (by decide)).elim
  · have hc : compositions 5 [1, 2, 3, 6]
        = [[1, 1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 3], [1, 2, 2], [2, 3]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    rcases hparts with rfl | rfl | rfl | rfl | rfl
    · exact (small (by decide)).elim
    · exact (small (by decide)).elim
    · exact (empty (by decide) sym_empty_113).elim
    · exact (small (by decide)).elim
    · exact (empty (by decide) sym_empty_23).elim
  · have hc : compositions 6 [1, 2, 3, 6]
        = [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2], [1, 1, 1, 3], [1, 1, 2, 2],
           [1, 2, 3], [2, 2, 2], [3, 3], [6]] := by
      simp [compositions, compositionsAux, legalSizes]
    rw [hc] at hparts
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hparts
    rcases hparts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (small (by decide)).elim
    · exact (small (by decide)).elim
    · exact (empty (by decide) sym_empty_1113).elim
    · exact (small (by decide)).elim
    · exact (empty (by decide) sym_empty_123).elim
    · exact (small (by decide)).elim
    · exact ⟨rfl, trident_unique_threeColoring_invariant hsub hinv hforced b hb⟩
    · exact (empty (by decide) sym_empty_6).elim

/-- Minimality: no valid S3-symmetric candidate has fewer than six auxiliary
    vertices (N ≤ 11). -/
theorem no_symmetric_gadget_below_six :
    ∀ k, k ≤ 5 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      (∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges) →
      (∀ s ∈ perms, ∀ e ∈ g, (threeColoring.attach parts).1.actEdge s e ∈ g) →
      (∀ f ∈ (threeColoring.attach parts).2, normEdge f ∈ g) →
      gadgetK threeColoring parts g false = none := by
  intro k hk parts hparts g hsub hinv hforced
  cases hb : gadgetK threeColoring parts g false with
  | none => rfl
  | some b =>
    exfalso
    obtain ⟨h33, _⟩ :=
      trident_minimum_unique k (by omega) parts hparts g hsub hinv hforced b hb
    have hsum := (compositions_sound hparts).1
    rw [h33] at hsum
    simp at hsum
    omega

end Atlas
