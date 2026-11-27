import search.CandidateTrident
import search.Search

/-!
  # The search of Section IV-D, tied to Definition 1 and to Theorem 16

  The exhaustive search of the paper's Section IV-D runs, for each orbit
  composition, over the S3-symmetric edge lists of a candidate space
  (`SymCandidate`), and judges each of them on the eight inputs (`gadgetK`).
  This file says what the candidate space is, that the search procedure
  visits all of it, and what the search returns. No statement uses a run of
  the search, and all depend on the standard axioms only.

  The candidate space and Definition 1.
  * `gadget_is_candidate`: every valid gadget of Definition 1 is, after a
    relabeling of its vertices, a candidate that passes the judge, and its
    orbit composition is in the list that the search visits.
  * `candidate_is_gadget`: every S3-symmetric candidate is a gadget of
    Definition 1, with as many auxiliary vertices as its composition
    counts, and it passes the judge exactly when the gadget is valid.

  Theorem 16 in the candidate space.
  * Statements 1 and 2: the trident, under its two labelings, is a candidate
    and passes the judge.
  * Statements 3 and 4: no candidate with at most five auxiliary vertices
    passes the judge, and one with at most six that passes is the trident.
    They follow from Theorem 16 (`proof/Theorem16.lean`).

  The search procedure (`searchSlice`).
  * `search_finds_every_valid_candidate`: every candidate that passes the
    judge is in the found list of the search.
  * `search_finds_only_valid_candidates`: every graph in the found list is a
    candidate that passes the judge.
  * `search_finds_every_valid_gadget`: so every valid gadget of
    Definition 1 is found.

  The outcome of the search.
  * `search_finds_nothing_below_six`, `search_finds_only_the_trident`,
    `search_finds_the_trident`: on the compositions with at most six
    auxiliary vertices the search returns the trident, under its two
    labelings, and nothing else.
  * `sym_empty_13` to `sym_empty_1113`: the six sweeps that the package
    `trident-symmetric-gadget-proof` of this repository re-runs with
    compiled code.
-/

namespace Def1

open Atlas

variable {V : Type}

-- ------------------------------------------ Definition 1 → the search space

/-- The search space covers Definition 1. Let `g` be a valid S3-symmetric
    clause gadget on a finite vertex set. Its auxiliary orbits, listed by
    size, are an orbit composition `g.parts` that the search visits; the
    relabeling `g.toVertex` of its vertices is injective, sends the literals
    and the anchors to those of the candidate space, commutes with the two
    actions, and turns adjacency into membership in the edge list
    `g.edgeList`; this edge list is an S3-symmetric candidate, and it passes
    the judge. -/
theorem gadget_is_candidate [Finite V] (g : Gadget V) (hv : g.Valid) :
    g.parts ∈ compositions (Nat.card {v // g.IsAux v}) [1, 2, 3, 6] ∧
    Statement.SymCandidate g.parts g.edgeList ∧
    gadgetK threeColoring g.parts g.edgeList false = some 1 ∧
    Function.Injective g.toVertex ∧
    (∀ i, g.toVertex (g.lit i) = .lit i.val) ∧
    g.toVertex g.gT = .aux g.parts.length 0 ∧
    g.toVertex g.gF = .aux (g.parts.length + 1) 0 ∧
    g.toVertex g.gB = .aux (g.parts.length + 2) 0 ∧
    (∀ σ v, g.toVertex (g.ρ σ v) = g.U.act (toTable σ) (g.toVertex v)) ∧
    (∀ u v, g.G.Adj u v ↔ normEdge (g.toVertex u, g.toVertex v) ∈ g.edgeList) := by
  have h1 : g.parts ∈ compositions (Nat.card {v // g.IsAux v}) [1, 2, 3, 6] :=
    (Statement.compositions_are_all_orbit_compositions _ _).mpr
      ⟨g.parts_sum, g.parts_legal, g.parts_sorted⟩
  have hT : g.toVertex g.gT = .aux g.parts.length 0 := by
    rw [g.toVertex_gT, g.parts_length]
  have hF : g.toVertex g.gF = .aux (g.parts.length + 1) 0 := by
    rw [g.toVertex_gF, g.parts_length]
  have hB : g.toVertex g.gB = .aux (g.parts.length + 2) 0 := by
    rw [g.toVertex_gB, g.parts_length]
  have hadj : ∀ u v, g.G.Adj u v ↔ normEdge (g.toVertex u, g.toVertex v) ∈ g.edgeList :=
    fun _ _ => g.adj_iff
  exact ⟨h1, g.symCandidate, g.gadgetK_of_valid hv, g.toVertex_injective, g.toVertex_lit,
    hT, hF, hB, g.toVertex_map, hadj⟩

-- ------------------------------------------ the search space → Definition 1

/-- The search space contains only gadgets of Definition 1. Let `C` be an
    S3-symmetric candidate: an orbit composition `C.parts` with part sizes
    in {1, 2, 3, 6} and an edge list `C.edges` in the candidate space that
    is closed under the engine's action and contains the forced edges. Then
    the vertices of the candidate space carry an S3-symmetric clause gadget
    `C.gadget` in the sense of Definition 1: its literals and anchors are
    those of the candidate space, two vertices are adjacent exactly when
    their normalized pair is in the edge list, and a permutation acts by
    the engine's action. This gadget has `C.parts.sum` auxiliary vertices,
    and it is valid exactly when the candidate passes the judge. -/
theorem candidate_is_gadget (C : Candidate) :
    (∀ i, (C.gadget.lit i).1 = .lit i.val) ∧
    C.gadget.gT.1 = .aux C.parts.length 0 ∧
    C.gadget.gF.1 = .aux (C.parts.length + 1) 0 ∧
    C.gadget.gB.1 = .aux (C.parts.length + 2) 0 ∧
    (∀ a b, C.gadget.G.Adj a b ↔ normEdge (a.1, b.1) ∈ C.edges) ∧
    (∀ σ v, (C.gadget.ρ σ v).1 = C.U.act (toTable σ) v.1) ∧
    Nat.card {v // C.gadget.IsAux v} = C.parts.sum ∧
    (C.gadget.Valid ↔ gadgetK threeColoring C.parts C.edges false = some 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, C.card_aux, C.valid_iff⟩
  · intro i
    rfl
  · rfl
  · rfl
  · rfl
  · intro a b
    exact C.adj_iff
  · intro σ v
    rfl

end Def1

-- ------------------------------------------ Theorem 16 in the candidate space

namespace Atlas.Statement

open Atlas Def1

/-- 1. The trident is an S3-symmetric candidate of composition `[3, 3]`,
    under each of its two labelings. -/
theorem trident_is_symmetric_candidate :
    SymCandidate [3, 3] tridentA ∧ SymCandidate [3, 3] tridentB :=
  tridentA_tridentB_symmetric

/-- 2. The trident passes the judge on all eight inputs, under each of its
    two labelings. -/
theorem trident_is_valid :
    gadgetK threeColoring [3, 3] tridentA false = some 1 ∧
    gadgetK threeColoring [3, 3] tridentB false = some 1 :=
  tridentA_tridentB_valid

/-- 3. Minimality in the candidate space: no S3-symmetric candidate with at
    most five auxiliary vertices passes the judge. The candidate is a
    gadget of Definition 1, and Theorem 16 applies; no run of the search is
    used. -/
theorem no_valid_symmetric_gadget_below_six_auxiliary_vertices :
    ∀ k, k ≤ 5 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g → gadgetK threeColoring parts g false = none :=
  no_symmetric_gadget_below_six

/-- 4. Uniqueness in the candidate space: every S3-symmetric candidate with
    at most six auxiliary vertices that passes the judge has composition
    `[3, 3]` and the edge set of the trident, under one of its two
    labelings. By Theorem 16 its gadget is isomorphic to the trident; the
    isomorphism commutes with the actions, which gives the composition and
    the labeling. No run of the search is used. -/
theorem valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident :
    ∀ k, k ≤ 6 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g →
      ∀ b, gadgetK threeColoring parts g false = some b →
        parts = [3, 3] ∧ b = 1 ∧
          ((∀ e, e ∈ g ↔ e ∈ tridentA) ∨ (∀ e, e ∈ g ↔ e ∈ tridentB)) :=
  trident_minimum_unique

-- --------------------------------------------------- the search procedure

/-- The search finds every valid candidate: an S3-symmetric candidate that
    passes the judge is in the found list of the search of its composition,
    up to the order of its edges. -/
theorem search_finds_every_valid_candidate :
    ∀ k, ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g → ∀ b, gadgetK threeColoring parts g false = some b →
        ∃ g', (g', b) ∈ (searchSlice threeColoring parts true).2.found ∧
          ∀ e, e ∈ g ↔ e ∈ g' := by
  intro k parts hparts g hsym b hK
  obtain ⟨-, hlegal, -⟩ := (compositions_are_all_orbit_compositions k parts).mp hparts
  exact searchSlice_complete parts hlegal hsym hK

/-- The search finds only valid candidates: every graph in the found list
    is an S3-symmetric candidate that passes the judge. -/
theorem search_finds_only_valid_candidates :
    ∀ k, ∀ parts ∈ compositions k [1, 2, 3, 6],
      ∀ x ∈ (searchSlice threeColoring parts true).2.found,
        SymCandidate parts x.1 ∧ gadgetK threeColoring parts x.1 false = some x.2 := by
  intro k parts hparts x hx
  obtain ⟨-, hlegal, -⟩ := (compositions_are_all_orbit_compositions k parts).mp hparts
  exact searchSlice_sound parts hlegal x hx

-- ------------------------------------------------- the outcome of the search

/-- The outcome of the search below six auxiliary vertices, without running
    it: on every orbit composition with at most five auxiliary vertices the
    search finds nothing. -/
theorem search_finds_nothing_below_six :
    ∀ k, k ≤ 5 → ∀ parts ∈ compositions k [1, 2, 3, 6],
      (searchSlice threeColoring parts true).2.found = [] := by
  intro k hk parts hparts
  refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
  obtain ⟨hsym, hK⟩ := search_finds_only_valid_candidates k parts hparts x hx
  rw [no_valid_symmetric_gadget_below_six_auxiliary_vertices k hk parts hparts x.1 hsym] at hK
  cases hK

/-- The outcome of the search with at most six auxiliary vertices, without
    running it: whatever the search finds is on the composition `[3, 3]`
    and has the edge set of the trident, under one of its two labelings. -/
theorem search_finds_only_the_trident :
    ∀ k, k ≤ 6 → ∀ parts ∈ compositions k [1, 2, 3, 6],
      ∀ x ∈ (searchSlice threeColoring parts true).2.found,
        parts = [3, 3] ∧ x.2 = 1 ∧
          ((∀ e, e ∈ x.1 ↔ e ∈ tridentA) ∨ (∀ e, e ∈ x.1 ↔ e ∈ tridentB)) := by
  intro k hk parts hparts x hx
  obtain ⟨hsym, hK⟩ := search_finds_only_valid_candidates k parts hparts x hx
  exact valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident k hk parts hparts
    x.1 hsym x.2 hK

/-- The search does find the trident, under each of its two labelings. -/
theorem search_finds_the_trident :
    (∃ g, (g, 1) ∈ (searchSlice threeColoring [3, 3] true).2.found ∧
      ∀ e, e ∈ tridentA ↔ e ∈ g) ∧
    (∃ g, (g, 1) ∈ (searchSlice threeColoring [3, 3] true).2.found ∧
      ∀ e, e ∈ tridentB ↔ e ∈ g) :=
  ⟨searchSlice_complete [3, 3] (by decide) trident_is_symmetric_candidate.1 trident_is_valid.1,
   searchSlice_complete [3, 3] (by decide) trident_is_symmetric_candidate.2 trident_is_valid.2⟩

/-- With six auxiliary vertices the search finds nothing outside the
    composition `[3, 3]`. -/
theorem search_finds_nothing_at_six_outside_trident_slice :
    ∀ parts ∈ compositions 6 [1, 2, 3, 6], parts ≠ [3, 3] →
      (searchSlice threeColoring parts true).2.found = [] := by
  intro parts hparts hne
  refine List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_
  exact hne (search_finds_only_the_trident 6 (Nat.le_refl 6) parts hparts x hx).1

end Atlas.Statement

namespace Atlas

open Statement

/-! ### The compiled sweeps of the search-based package, as theorems

  The package `trident-symmetric-gadget-proof` of this repository obtains
  the six statements below by running the search at build time with compiled
  code (`native_decide`, about 8.5 hours). Here they have the same names and
  the same statements, and they follow from Theorem 16 without a run. -/

theorem sym_empty_13 : (searchSlice threeColoring [1, 3] true).2.found = [] :=
  search_finds_nothing_below_six 4 (by decide) [1, 3]
    ((compositions_are_all_orbit_compositions 4 [1, 3]).mpr ⟨rfl, by decide, by decide⟩)

theorem sym_empty_23 : (searchSlice threeColoring [2, 3] true).2.found = [] :=
  search_finds_nothing_below_six 5 (by decide) [2, 3]
    ((compositions_are_all_orbit_compositions 5 [2, 3]).mpr ⟨rfl, by decide, by decide⟩)

theorem sym_empty_113 : (searchSlice threeColoring [1, 1, 3] true).2.found = [] :=
  search_finds_nothing_below_six 5 (by decide) [1, 1, 3]
    ((compositions_are_all_orbit_compositions 5 [1, 1, 3]).mpr ⟨rfl, by decide, by decide⟩)

theorem sym_empty_6 : (searchSlice threeColoring [6] true).2.found = [] :=
  search_finds_nothing_at_six_outside_trident_slice [6]
    ((compositions_are_all_orbit_compositions 6 [6]).mpr ⟨rfl, by decide, by decide⟩)
    (by decide)

theorem sym_empty_123 : (searchSlice threeColoring [1, 2, 3] true).2.found = [] :=
  search_finds_nothing_at_six_outside_trident_slice [1, 2, 3]
    ((compositions_are_all_orbit_compositions 6 [1, 2, 3]).mpr ⟨rfl, by decide, by decide⟩)
    (by decide)

theorem sym_empty_1113 : (searchSlice threeColoring [1, 1, 1, 3] true).2.found = [] :=
  search_finds_nothing_at_six_outside_trident_slice [1, 1, 1, 3]
    ((compositions_are_all_orbit_compositions 6 [1, 1, 1, 3]).mpr ⟨rfl, by decide, by decide⟩)
    (by decide)

end Atlas

namespace Def1

open Atlas

/-- The search covers Definition 1: every valid S3-symmetric clause gadget on
    a finite vertex set is found by the search. Its orbit composition
    `g.parts` is one of the compositions that the search visits, and the
    found list of that composition contains the relabeled edge list of the
    gadget, up to the order of its edges. -/
theorem search_finds_every_valid_gadget {V : Type} [Finite V] (g : Gadget V) (hv : g.Valid) :
    g.parts ∈ compositions (Nat.card {v // g.IsAux v}) [1, 2, 3, 6] ∧
    ∃ g', (g', 1) ∈ (searchSlice threeColoring g.parts true).2.found ∧
      ∀ e, e ∈ g.edgeList ↔ e ∈ g' := by
  obtain ⟨h1, hsym, hK, -⟩ := gadget_is_candidate g hv
  exact ⟨h1, searchSlice_complete g.parts g.parts_legal hsym hK⟩

end Def1

-- The statements of this file depend on the standard axioms only. The build
-- fails if one of them depends on any other axiom.
/--
info: 'Def1.gadget_is_candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.gadget_is_candidate

/--
info: 'Def1.candidate_is_gadget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.candidate_is_gadget

/--
info: 'Def1.search_finds_every_valid_gadget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.search_finds_every_valid_gadget

/--
info: 'Atlas.Statement.search_finds_nothing_below_six' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Atlas.Statement.search_finds_nothing_below_six

/--
info: 'Atlas.Statement.search_finds_only_the_trident' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Atlas.Statement.search_finds_only_the_trident

/--
info: 'Atlas.Statement.search_finds_the_trident' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Atlas.Statement.search_finds_the_trident

/--
info: 'Atlas.sym_empty_1113' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Atlas.sym_empty_1113
