import atlas.CandidateValid
import atlas.TridentGadget

/-!
  # Theorem 16 of the paper for Definition 1

  The two results at the end of this file are stated with the definitions
  of `Definition1.lean` only (Mathlib's simple graphs and permutations; no
  engine definitions).

  * `trident_is_valid_gadget`: the trident, with its literals and anchors,
    is a valid S3-symmetric clause gadget with six auxiliary vertices.
  * `minimum_unique`: every valid S3-symmetric clause gadget on a finite
    vertex set has at least six auxiliary vertices, added to its six fixed
    vertices (the literals and the anchors), and one with exactly six is
    isomorphic to the trident by an isomorphism that fixes each literal and
    each anchor.

  Proof of `minimum_unique`. Lemma 6 (`OrbitStructure.lean`) turns the
  gadget into a symmetric candidate of the search engine (`Candidate.lean`,
  `CandidateGraph.lean`), a valid gadget passes the engine's judge
  (`CandidateValid.lean`), and Statements 3 and 4 of `Statement.lean` (the
  exhaustive search) say that no candidate with fewer than six auxiliary
  vertices passes and that one with six is the trident under one of its two
  labelings. Both labelings are isomorphic to the trident graph of
  `Definition1.lean` (checked edge by edge below).

  The results are about gadgets on the six fixed vertices of Definition 1
  (three literals and the palette triangle) and count the auxiliary vertices
  added to them. They are not about arbitrary graphs with at most twelve
  vertices.
-/

namespace Def1

open Atlas

variable {V : Type}

-- ------------------------------------------ the two labelings of the trident

/-- The index `j` as an element of `Fin 3`. -/
def idx (j : Nat) : Fin 3 := ⟨j % 3, Nat.mod_lt j (by decide)⟩

theorem idx_val (i : Fin 3) : idx i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- The vertices of the candidate space of `[3, 3]` as vertices of the
    trident, for the labeling `tridentA`: part 0 holds the branch vertices
    and part 1 the upper triangle. -/
def toTVA : Vertex → TV
  | .lit i => .x (idx i)
  | .aux 0 j => .p (idx j)
  | .aux 1 j => .u (idx j)
  | .aux 2 _ => .gT
  | .aux 3 _ => .gF
  | .aux _ _ => .gB

/-- The same for the labeling `tridentB`: part 1 holds the branch vertices
    and part 0 the upper triangle. -/
def toTVB : Vertex → TV
  | .lit i => .x (idx i)
  | .aux 0 j => .u (idx j)
  | .aux 1 j => .p (idx j)
  | .aux 2 _ => .gT
  | .aux 3 _ => .gF
  | .aux _ _ => .gB

/-- Check of data: `toTVA` is injective on the twelve vertices. -/
theorem toTVA_inj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
    ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices, toTVA a = toTVA b → a = b := by
  decide

theorem toTVB_inj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
    ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices, toTVB a = toTVB b → a = b := by
  decide

/-- Check of data: the edge list `tridentA` of the engine is the trident
    graph of `Definition1.lean`, pair by pair. -/
theorem toTVA_adj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
    ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices,
      (normEdge (a, b) ∈ tridentA ↔ trident.Adj (toTVA a) (toTVA b)) := by
  decide

theorem toTVB_adj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
    ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices,
      (normEdge (a, b) ∈ tridentB ↔ trident.Adj (toTVB a) (toTVB b)) := by
  decide

namespace Gadget

variable (g : Gadget V) [Finite V]

-- --------------------------------------------------- counting the vertices

/-- The six named vertices: the literals and the anchors. -/
def named : Fin 3 ⊕ Fin 3 → V := Sum.elim g.lit ![g.gT, g.gF, g.gB]

theorem toVertex_named_inr (j : Fin 3) :
    g.toVertex (g.named (.inr j)) = .aux (g.m + j.val) 0 := by
  fin_cases j
  · exact g.toVertex_gT
  · exact g.toVertex_gF
  · exact g.toVertex_gB

omit [Finite V] in
theorem not_isAux_named (r : Fin 3 ⊕ Fin 3) : ¬ g.IsAux (g.named r) := by
  intro h
  rcases r with i | j
  · exact h.1 i rfl
  · fin_cases j
    · exact h.2.1 rfl
    · exact h.2.2.1 rfl
    · exact h.2.2.2 rfl

theorem named_injective : Function.Injective g.named := by
  intro r r' h
  have ht := congrArg g.toVertex h
  rcases r with i | j <;> rcases r' with i' | j'
  · have h1 : g.toVertex (g.lit i) = g.toVertex (g.lit i') := ht
    rw [toVertex_lit, toVertex_lit] at h1
    rw [Fin.ext (Vertex.lit.inj h1)]
  · have h1 : g.toVertex (g.lit i) = g.toVertex (g.named (.inr j')) := ht
    rw [toVertex_lit, toVertex_named_inr] at h1
    exact Vertex.noConfusion h1
  · have h1 : g.toVertex (g.named (.inr j)) = g.toVertex (g.lit i') := ht
    rw [toVertex_lit, toVertex_named_inr] at h1
    exact Vertex.noConfusion h1
  · rw [toVertex_named_inr, toVertex_named_inr] at ht
    have h1 := (Vertex.aux.inj ht).1
    rw [Fin.ext (Nat.add_left_cancel h1)]

/-- Every vertex is an auxiliary vertex or one of the six named ones. -/
theorem sum_bijective :
    Function.Bijective (Sum.elim (Subtype.val : g.Aux → V) g.named) := by
  constructor
  · intro x y h
    rcases x with a | r <;> rcases y with b | r'
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 : a.1 = g.named r' := h
      exact absurd (h1 ▸ a.2) (g.not_isAux_named r')
    · have h1 : g.named r = b.1 := h
      exact absurd (h1 ▸ b.2) (g.not_isAux_named r)
    · exact congrArg Sum.inr (g.named_injective h)
  · intro v
    rcases g.vertex_cases v with ⟨i, rfl⟩ | rfl | rfl | rfl | ⟨a, rfl⟩
    · exact ⟨.inr (.inl i), rfl⟩
    · exact ⟨.inr (.inr 0), rfl⟩
    · exact ⟨.inr (.inr 1), rfl⟩
    · exact ⟨.inr (.inr 2), rfl⟩
    · exact ⟨.inl a, rfl⟩

/-- The number of vertices is the number of auxiliary vertices plus six. -/
theorem card_eq : Nat.card V = Nat.card g.Aux + 6 := by
  have h3 : Nat.card (Fin 3) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← Nat.card_congr (Equiv.ofBijective _ g.sum_bijective), Nat.card_sum, Nat.card_sum, h3]

/-- The orbit composition of the gadget is one of the engine's
    compositions (Statement 5). -/
theorem parts_mem_compositions :
    g.parts ∈ compositions (Nat.card g.Aux) [1, 2, 3, 6] :=
  (Statement.compositions_are_all_orbit_compositions _ _).mpr
    ⟨g.parts_sum, g.parts_legal, g.parts_sorted⟩

-- ------------------------------------------------ back to the trident graph

/-- A twelve-vertex gadget whose candidate has composition `[3, 3]` and the
    edge set `T` is isomorphic to the trident, given a map `ψ` from the
    candidate's vertices to the trident's that is injective and matches
    `T` with the trident's edges. -/
theorem iso_of_map [Fintype V] (h12 : Fintype.card V = 12) (hparts : g.parts = [3, 3])
    (T : List Edge) (hT : ∀ e, e ∈ g.edgeList ↔ e ∈ T) (ψ : Vertex → TV)
    (hinj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
      ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices, ψ a = ψ b → a = b)
    (hadj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
      ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices,
        (normEdge (a, b) ∈ T ↔ trident.Adj (ψ a) (ψ b)))
    (hlit : ∀ i : Fin 3, ψ (.lit i.val) = TV.x i) (hgT : ψ (.aux 2 0) = TV.gT)
    (hgF : ψ (.aux 3 0) = TV.gF) (hgB : ψ (.aux 4 0) = TV.gB) :
    ∃ e : g.G ≃g trident,
      (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB := by
  have hm : g.m = 2 := by
    rw [← g.parts_length, hparts]
    rfl
  have hmem : ∀ v, g.toVertex v ∈ (threeColoring.attach [3, 3]).1.vertices := by
    intro v
    have h := g.toVertex_mem v
    unfold U at h
    rwa [hparts] at h
  have hinj' : Function.Injective fun v => ψ (g.toVertex v) := by
    intro u v h
    exact g.toVertex_injective (hinj _ (hmem u) _ (hmem v) h)
  have hbij : Function.Bijective fun v => ψ (g.toVertex v) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj', by rw [h12, card_TV]⟩
  refine ⟨⟨Equiv.ofBijective _ hbij, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro u v
    show trident.Adj (ψ (g.toVertex u)) (ψ (g.toVertex v)) ↔ g.G.Adj u v
    rw [g.adj_iff, hT, hadj _ (hmem u) _ (hmem v)]
  · intro i
    show ψ (g.toVertex (g.lit i)) = TV.x i
    rw [toVertex_lit]
    exact hlit i
  · show ψ (g.toVertex g.gT) = TV.gT
    rw [toVertex_gT, hm]
    exact hgT
  · show ψ (g.toVertex g.gF) = TV.gF
    rw [toVertex_gF, hm]
    exact hgF
  · show ψ (g.toVertex g.gB) = TV.gB
    rw [toVertex_gB, hm]
    exact hgB

end Gadget

-- ------------------------------------------------------------- the theorem

/-- Theorem 16 of the paper (minimum size and uniqueness), for Definition 1.
    Let `g` be a valid S3-symmetric clause gadget on a finite vertex set:
    its six fixed vertices are the three literals and the three anchors, and
    its other vertices are auxiliary. Then `g` has at least six auxiliary
    vertices, and so at least twelve vertices in total. If it has exactly
    six auxiliary vertices, it is the trident: there is a graph isomorphism
    onto the trident that sends each literal to the corresponding literal
    and each anchor to the corresponding anchor. -/
theorem minimum_unique [Fintype V] (g : Gadget V) (hv : g.Valid) :
    6 ≤ Nat.card {v // g.IsAux v} ∧ 12 ≤ Fintype.card V ∧
    (Nat.card {v // g.IsAux v} = 6 → ∃ e : g.G ≃g trident,
      (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB) := by
  have hcard : Fintype.card V = Nat.card {v // g.IsAux v} + 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact g.card_eq
  have hK := g.gadgetK_of_valid hv
  have hmem : g.parts ∈ compositions (Nat.card {v // g.IsAux v}) [1, 2, 3, 6] :=
    g.parts_mem_compositions
  have hsym := g.symCandidate
  -- at least six auxiliary vertices: Statement 3
  have hsix : 6 ≤ Nat.card {v // g.IsAux v} := by
    by_contra hlt
    have hk : Nat.card {v // g.IsAux v} ≤ 5 := by omega
    have hnone :=
      Statement.no_valid_symmetric_gadget_below_six_auxiliary_vertices _ hk _ hmem _ hsym
    rw [hnone] at hK
    cases hK
  refine ⟨hsix, by omega, fun h6 => ?_⟩
  -- exactly six auxiliary vertices: Statement 4
  have h12 : Fintype.card V = 12 := by omega
  obtain ⟨hparts, -, hedges⟩ :=
    Statement.valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident _ (le_of_eq h6) _
      hmem _ hsym 1 hK
  rcases hedges with hA | hB
  · exact g.iso_of_map h12 hparts tridentA hA toTVA toTVA_inj toTVA_adj
      (fun i => congrArg TV.x (idx_val i)) rfl rfl rfl
  · exact g.iso_of_map h12 hparts tridentB hB toTVB toTVB_inj toTVB_adj
      (fun i => congrArg TV.x (idx_val i)) rfl rfl rfl

/-- The trident attains the minimum: the trident graph, with the literals
    `TV.x i` and the anchors `TV.gT`, `TV.gF`, `TV.gB`, carries an
    S3-symmetric clause gadget in the sense of Definition 1, this gadget is
    valid, and it has six auxiliary vertices (the `TV.p i` and the
    `TV.u i`), twelve vertices in total. -/
theorem trident_is_valid_gadget :
    (∃ g : Gadget TV, g.G = trident ∧ g.lit = TV.x ∧ g.gT = TV.gT ∧ g.gF = TV.gF ∧
      g.gB = TV.gB ∧ g.Valid ∧ Nat.card {v // g.IsAux v} = 6) ∧ Fintype.card TV = 12 :=
  ⟨⟨tridentGadget, rfl, rfl, rfl, rfl, rfl, tridentGadget_valid, tridentGadget_card_aux⟩,
    card_TV⟩

end Def1

#print axioms Def1.trident_is_valid_gadget
#print axioms Def1.minimum_unique
