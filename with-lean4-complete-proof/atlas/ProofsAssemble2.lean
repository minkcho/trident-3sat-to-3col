import atlas.Assemble2
import atlas.ProofsAssemble
import atlas.ProofsLib
/-!
  Theorems for the generalized assembler (`atlas/Assemble2.lean`),
  following the promotion priorities of `assembler-taxonomy.md` section 6:

  (1) the subsumption theorem -- Phase 1 IS the by-literal quotient of the
      occurrence-level carrier: `phase1Assemble = assemble`, propositionally
      (a zip-vs-range reindexing plus the mapping-function identity
      `mergeByLiteral_occMapVertex`);
  (2) the occurrence-level interface theorem -- with an aux-free wiring, no
      assembled edge joins auxiliary copies of two different clauses.

  Row 2's semantic theorem (max clique over active occurrences = number of
  satisfied clauses, for every formula and assignment) lives in
  `atlas/ProofsOcc.lean`.
-/

namespace Atlas

open List

-- --------------------------------------------------- (1) subsumption

/-- Pointwise: quotienting the occurrence placement by the literal merge is
    exactly the Phase-1 placement. -/
theorem mergeByLiteral_occMapVertex (P : Problem) (own c : Nat)
    (clauses : List ClauseSpec) (v : Vertex) :
    mergeByLiteral clauses (occMapVertex P own c v)
      = mapVertex P own c (clauses.getD c []) v := by
  cases v with
  | lit i => rfl
  | aux p j =>
    simp only [occMapVertex, mapVertex]
    split
    · rfl
    · split
      · rfl
      · rfl

/-- The subsumption theorem: Phase 1 is the by-literal quotient of the
    general assembler -- it reproduces `assemble` verbatim, for every
    problem, gadget and clause list. -/
theorem phase1Assemble_eq_assemble (P : Problem) (parts : List Nat)
    (g : List Edge) (clauses : List ClauseSpec) :
    phase1Assemble P parts g clauses = assemble P parts g clauses := by
  simp only [phase1Assemble, assembleVia, assemble,
    zipRange_flatMap ([] : ClauseSpec) (fun p : Nat × ClauseSpec =>
      g.map fun e =>
        normM (mapVertex P parts.length p.1 p.2 e.1,
               mapVertex P parts.length p.1 p.2 e.2)),
    mergeByLiteral_occMapVertex]

-- ------------------------------------ (2) occurrence-level interface

/-- Which clause's private copy an occurrence-carrier vertex belongs to
    (`none` = shared or an occurrence port; ports are allowed to interact
    across clauses -- that is what the wiring is for). -/
def OVertex.auxClauseOf : OVertex → Option Nat
  | .aux c _ _ => some c
  | _ => none

theorem occMapVertex_auxClauseOf (P : Problem) (own c : Nat) (v : Vertex) :
    (occMapVertex P own c v).auxClauseOf = none ∨
    (occMapVertex P own c v).auxClauseOf = some c := by
  cases v with
  | lit i => exact Or.inl rfl
  | aux p j =>
    simp only [occMapVertex]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem normO_fst_snd (a b : OVertex) :
    ((normO (a, b)).1 = a ∧ (normO (a, b)).2 = b) ∨
    ((normO (a, b)).1 = b ∧ (normO (a, b)).2 = a) := by
  unfold normO
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- The interface theorem at the occurrence level: with an aux-free wiring,
    no assembled edge joins auxiliary copies of two different clauses --
    clause copies interact only through their occurrence ports and the
    shared anchors. -/
theorem occAssemble_interface (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) (wiring : List OEdge)
    (hwiring : ∀ e ∈ wiring,
      OVertex.auxClauseOf e.1 = none ∧ OVertex.auxClauseOf e.2 = none) :
    ∀ e ∈ (occAssemble P parts g clauses wiring).2, ∀ c₁ c₂,
      OVertex.auxClauseOf e.1 = some c₁ → OVertex.auxClauseOf e.2 = some c₂ →
      c₁ = c₂ := by
  intro e he c₁ c₂ h1 h2
  simp only [occAssemble, assembleVia, id_eq] at he
  have he' := (List.mem_filter.mp he).1
  rw [List.mem_eraseDups] at he'
  have key : ∀ c : Nat, ∀ x y : OVertex,
      (x.auxClauseOf = none ∨ x.auxClauseOf = some c) →
      (y.auxClauseOf = none ∨ y.auxClauseOf = some c) →
      x.auxClauseOf = some c₁ → y.auxClauseOf = some c₂ → c₁ = c₂ := by
    intro c x y hx hy hx1 hy2
    rcases hx with h | h
    · rw [h] at hx1
      cases hx1
    · rcases hy with h' | h'
      · rw [h'] at hy2
        cases hy2
      · rw [h] at hx1
        rw [h'] at hy2
        exact (Option.some.inj hx1).symm.trans (Option.some.inj hy2)
  rcases List.mem_append.mp he' with hcopy | hlay
  · obtain ⟨c, _, hmap⟩ := List.mem_flatMap.mp hcopy
    obtain ⟨e₀, _, rfl⟩ := List.mem_map.mp hmap
    rcases normO_fst_snd (occMapVertex P parts.length c e₀.1)
        (occMapVertex P parts.length c e₀.2) with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · rw [hf] at h1
      rw [hs] at h2
      exact key c _ _ (occMapVertex_auxClauseOf P parts.length c e₀.1)
        (occMapVertex_auxClauseOf P parts.length c e₀.2) h1 h2
    · rw [hf] at h1
      rw [hs] at h2
      exact key c _ _ (occMapVertex_auxClauseOf P parts.length c e₀.2)
        (occMapVertex_auxClauseOf P parts.length c e₀.1) h1 h2
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hlay
    obtain ⟨a, b⟩ := e₀
    have hL1 : OVertex.auxClauseOf a = none := (hwiring (a, b) he₀).1
    have hL2 : OVertex.auxClauseOf b = none := (hwiring (a, b) he₀).2
    rcases normO_fst_snd a b with ⟨hf, _⟩ | ⟨hf, _⟩
    · rw [hf] at h1
      rw [hL1] at h1
      cases h1
    · rw [hf] at h1
      rw [hL2] at h1
      cases h1

end Atlas
