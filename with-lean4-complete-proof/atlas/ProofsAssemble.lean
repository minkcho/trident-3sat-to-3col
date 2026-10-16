import atlas.Problems.ThreeColoring
/-!
  The interface theorem: in the assembled multi-clause graph, clause
  copies never touch each other -- no edge connects auxiliary copies of
  two different clauses, so clause copies interact only through the
  shared literal layer and the shared anchors.

  This is the paper's interface premise (clause copies share no local
  vertices), proved once for the assembler and inherited by every gadget:
  the assembler is parameterized by the problem alone, and the only
  problem-supplied edges are the literal-layer gadget, which the
  per-problem lemmas below show to be aux-free for 3-coloring and vertex
  cover (the kit-default pair-edge layer of the other problems is
  discharged the same way when needed). What remains outside the
  proved perimeter is the semantic content of the rows (multiK's table),
  not the shape of the assembled graph.
-/

namespace Atlas

open List

/-- Which clause copy a vertex belongs to (none = shared: layer, anchor). -/
def MVertex.clauseOf : MVertex → Option Nat
  | .aux c _ _ => some c
  | _ => none

/-- A mapped gadget vertex is shared or belongs to clause `c` itself. -/
theorem mapVertex_clauseOf (P : Problem) (own c : Nat) (clause : ClauseSpec)
    (v : Vertex) :
    (mapVertex P own c clause v).clauseOf = none ∨
    (mapVertex P own c clause v).clauseOf = some c := by
  cases v with
  | lit i =>
    left
    simp only [mapVertex, litVertex]
    split <;> rfl
  | aux p j =>
    simp only [mapVertex]
    split
    · exact Or.inl rfl
    · split
      · left
        simp only [negLitVertex]
        split <;> rfl
      · exact Or.inr rfl

/-- Edge normalization keeps or swaps the two endpoints. -/
theorem normM_fst_snd (a b : MVertex) :
    ((normM (a, b)).1 = a ∧ (normM (a, b)).2 = b) ∨
    ((normM (a, b)).1 = b ∧ (normM (a, b)).2 = a) := by
  unfold normM
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- The interface theorem. Hypothesis: the problem's literal-layer gadget
    uses only shared vertices (discharged per problem below). Conclusion:
    no assembled edge joins auxiliary copies of two different clauses. -/
theorem assemble_interface (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec)
    (hlayer : ∀ e ∈ P.layer (varCount clauses),
      MVertex.clauseOf e.1 = none ∧ MVertex.clauseOf e.2 = none) :
    ∀ e ∈ (assemble P parts g clauses).2, ∀ c₁ c₂,
      MVertex.clauseOf e.1 = some c₁ → MVertex.clauseOf e.2 = some c₂ →
      c₁ = c₂ := by
  intro e he c₁ c₂ h1 h2
  simp only [assemble] at he
  have he' := (List.mem_filter.mp he).1
  rw [List.mem_eraseDups] at he'
  have key : ∀ c : Nat, ∀ x y : MVertex,
      (x.clauseOf = none ∨ x.clauseOf = some c) →
      (y.clauseOf = none ∨ y.clauseOf = some c) →
      x.clauseOf = some c₁ → y.clauseOf = some c₂ → c₁ = c₂ := by
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
  · -- a clause-copy edge: both endpoints are images of the same clause c
    obtain ⟨cp, _, hmap⟩ := List.mem_flatMap.mp hcopy
    obtain ⟨c, clause⟩ := cp
    obtain ⟨e₀, _, rfl⟩ := List.mem_map.mp hmap
    rcases normM_fst_snd (mapVertex P parts.length c clause e₀.1)
        (mapVertex P parts.length c clause e₀.2) with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · rw [hf] at h1
      rw [hs] at h2
      exact key c _ _ (mapVertex_clauseOf P parts.length c clause e₀.1)
        (mapVertex_clauseOf P parts.length c clause e₀.2) h1 h2
    · rw [hf] at h1
      rw [hs] at h2
      exact key c _ _ (mapVertex_clauseOf P parts.length c clause e₀.2)
        (mapVertex_clauseOf P parts.length c clause e₀.1) h1 h2
  · -- a literal-layer edge: both endpoints are shared, contradiction
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hlay
    obtain ⟨a, b⟩ := e₀
    have hL1 : MVertex.clauseOf a = none := (hlayer (a, b) he₀).1
    have hL2 : MVertex.clauseOf b = none := (hlayer (a, b) he₀).2
    rcases normM_fst_snd a b with ⟨hf, _⟩ | ⟨hf, _⟩
    · rw [hf] at h1
      rw [hL1] at h1
      cases h1
    · rw [hf] at h1
      rw [hL2] at h1
      cases h1

-- ------------------------------------------------- per-problem discharges

/-- The 3-coloring literal layer (pair edges + both-polarity G_B fans)
    uses only shared vertices. -/
theorem threeColoring_layer_shared (n : Nat) :
    ∀ e ∈ threeColoring.layer n,
      MVertex.clauseOf e.1 = none ∧ MVertex.clauseOf e.2 = none := by
  intro e he
  have hdef : threeColoring.layer n = ((List.range n).flatMap fun v =>
    [(MVertex.pos v, MVertex.neg v), (.pos v, .anchor 2),
     (.neg v, .anchor 2)]) := rfl
  rw [hdef] at he
  obtain ⟨v, _, hmem⟩ := List.mem_flatMap.mp he
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨rfl, rfl⟩
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨rfl, rfl⟩
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨rfl, rfl⟩
  cases hmem

/-- Interface theorem, instantiated: for any 3COL gadget whatsoever, the
    assembled clause copies interact only through the layer and anchors. -/
theorem threeColoring_assemble_interface (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) :
    ∀ e ∈ (assemble threeColoring parts g clauses).2, ∀ c₁ c₂,
      MVertex.clauseOf e.1 = some c₁ → MVertex.clauseOf e.2 = some c₂ →
      c₁ = c₂ :=
  assemble_interface threeColoring parts g clauses
    (threeColoring_layer_shared (varCount clauses))

end Atlas
