import proof.Uniqueness
import search.CandidateGadget
import search.Trident

/-!
  Theorem 16 in the candidate space, without a run of the search.

  A candidate that passes the judge is a valid gadget of Definition 1
  (`CandidateGadget.lean`), so Theorem 16 applies to it: it has at least six
  auxiliary vertices (`no_symmetric_gadget_below_six`), and with six its
  graph is isomorphic to the trident.

  To name the candidate, the isomorphism is traced back to the labels of
  the candidate space (`trident_minimum_unique`). The isomorphism commutes
  with the two actions (`proof/Uniqueness.lean`), so a vertex and its image
  have the same stabilizer. The image of the first vertex of a part is a
  `p_j` or a `u_j`, whose stabilizer is the stabilizer of the index `j`;
  the engine's action on a part of size 1, 2, 3 or 6 has the stabilizers of
  `stdAct_zero`. Hence every part has size 3, the composition is `[3, 3]`,
  and the two parts are the branch layer and the upper triangle, in one of
  the two orders: the edge list is `tridentA` or `tridentB`.
-/

namespace Def1

open Atlas

-- ---------------------------------------------- the parts of a trident

/-- Table check of the engine's action: the permutations that fix the first
    vertex of a part of size 1, 2, 3 and 6 are all permutations, the even
    ones, those that fix the index 0, and the identity. -/
theorem stdAct_zero : ∀ σ : Equiv.Perm (Fin 3),
    stdAct 1 (toTable σ) 0 = 0 ∧
    (stdAct 2 (toTable σ) 0 = 0 ↔ Equiv.Perm.sign σ = 1) ∧
    (stdAct 3 (toTable σ) 0 = 0 ↔ σ 0 = 0) ∧
    (stdAct 6 (toTable σ) 0 = 0 ↔ σ = 1) := by decide

/-- A list of 3s with sum 6 is `[3, 3]`. -/
theorem eq_three_three : ∀ l : List Nat, (∀ x ∈ l, x = 3) → l.sum = 6 → l = [3, 3]
  | [], _, hs => by simp at hs
  | [a], h, hs => by
    have ha := h a (by simp)
    simp at hs
    omega
  | [a, b], h, _ => by rw [h a (by simp), h b (by simp)]
  | a :: b :: c :: t, h, hs => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hc := h c (by simp)
    simp at hs
    omega

namespace Candidate

variable (C : Candidate)

theorem size_eq {p : Nat} (hp : p < C.parts.length) : C.U.size p = C.parts[p] := by
  show (C.parts ++ [1, 1, 1]).getD p 0 = C.parts[p]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hp, List.getElem?_eq_getElem hp]
  rfl

/-- A part of a candidate whose gadget is the trident. Let `e` be the
    isomorphism onto the trident that fixes the literals and the anchors.
    It commutes with the actions, so the first vertex of a part and its
    image have the same stabilizer. The image is a `p_j` or a `u_j`, whose
    stabilizer is the stabilizer of the index `j`. Hence the part has size
    3, and `e` sends its vertices, in order, to the `p_i` or to the
    `u_i`. -/
theorem part_of_trident (e : C.gadget.G ≃g trident)
    (he : (∀ i, e (C.gadget.lit i) = TV.x i) ∧ e C.gadget.gT = TV.gT ∧
      e C.gadget.gF = TV.gF ∧ e C.gadget.gB = TV.gB)
    {p : Nat} (hp : p < C.parts.length) :
    C.U.size p = 3 ∧
    ((∀ i (h : Vertex.aux p i ∈ C.U.vertices), e ⟨.aux p i, h⟩ = TV.p (idx i)) ∨
     (∀ i (h : Vertex.aux p i ∈ C.U.vertices), e ⟨.aux p i, h⟩ = TV.u (idx i))) := by
  have hlen : p < C.U.parts.length := by
    show p < (C.parts ++ [1, 1, 1]).length
    rw [List.length_append]
    omega
  have hsz := legal_size C.U_legal hlen
  have h0 : Vertex.aux p 0 ∈ C.U.vertices :=
    mem_vertices.mpr (Or.inr ⟨p, 0, hlen, by rcases hsz with h | h | h | h <;> omega, rfl⟩)
  -- the image of the first vertex is an auxiliary vertex of the trident
  have hx : ∀ i, e ⟨.aux p 0, h0⟩ ≠ TV.x i := fun i h =>
    Vertex.noConfusion (congrArg Subtype.val (e.injective (h.trans (he.1 i).symm)))
  have hanch : ∀ d : Fin 3, (⟨.aux p 0, h0⟩ : C.Vert) ≠ C.anchorV d := by
    intro d h
    have h1 : p = C.parts.length + d.val := (Vertex.aux.inj (congrArg Subtype.val h)).1
    omega
  have hT : e ⟨.aux p 0, h0⟩ ≠ TV.gT := fun h => hanch 0 (e.injective (h.trans he.2.1.symm))
  have hF : e ⟨.aux p 0, h0⟩ ≠ TV.gF := fun h => hanch 1 (e.injective (h.trans he.2.2.1.symm))
  have hB : e ⟨.aux p 0, h0⟩ ≠ TV.gB := fun h => hanch 2 (e.injective (h.trans he.2.2.2.symm))
  have hcases : ∃ j : Fin 3, e ⟨.aux p 0, h0⟩ = TV.p j ∨ e ⟨.aux p 0, h0⟩ = TV.u j := by
    cases hv : e ⟨.aux p 0, h0⟩ with
    | x i => exact absurd hv (hx i)
    | p j => exact ⟨j, Or.inl rfl⟩
    | u j => exact ⟨j, Or.inr rfl⟩
    | gT => exact absurd hv hT
    | gF => exact absurd hv hF
    | gB => exact absurd hv hB
  obtain ⟨j, hj⟩ := hcases
  -- the action on the vertices of the part, in the engine's labels
  have hval : ∀ (σ : Equiv.Perm (Fin 3)) (i : Nat) (h : Vertex.aux p i ∈ C.U.vertices),
      (C.gadget.ρ σ ⟨.aux p i, h⟩).1 = .aux p (stdAct (C.U.size p) (toTable σ) i) :=
    fun σ i _ => act_aux_std C.U (toTable σ) p i
  -- the first vertex and its image have the same stabilizer
  have hstab : ∀ σ : Equiv.Perm (Fin 3),
      stdAct (C.U.size p) (toTable σ) 0 = 0 ↔ σ j = j := by
    intro σ
    have heq := iso_trident_equivariant C.gadget e he σ ⟨.aux p 0, h0⟩
    constructor
    · intro hs
      have hfix : C.gadget.ρ σ ⟨.aux p 0, h0⟩ = ⟨.aux p 0, h0⟩ :=
        Subtype.ext (by rw [hval σ 0 h0, hs])
      rw [hfix] at heq
      rcases hj with hj | hj
      · rw [hj] at heq
        have h2 : TV.p j = TV.p (σ j) := heq
        exact (TV.p.inj h2).symm
      · rw [hj] at heq
        have h2 : TV.u j = TV.u (σ j) := heq
        exact (TV.u.inj h2).symm
    · intro hs
      have h2 : e (C.gadget.ρ σ ⟨.aux p 0, h0⟩) = e ⟨.aux p 0, h0⟩ := by
        rw [heq]
        rcases hj with hj | hj
        · rw [hj]
          show TV.p (σ j) = TV.p j
          rw [hs]
        · rw [hj]
          show TV.u (σ j) = TV.u j
          rw [hs]
      have h3 := congrArg Subtype.val (e.injective h2)
      rw [hval σ 0 h0] at h3
      exact (Vertex.aux.inj h3).2
  -- so the part has size 3, and the image has index 0
  have hsize : C.U.size p = 3 ∧ j = 0 := by
    rcases hsz with h | h | h | h
    · exfalso
      rw [h] at hstab
      obtain ⟨a, haj, -⟩ := exists_third j j
      have h1 := (hstab (Equiv.swap j a)).mp (stdAct_zero _).1
      rw [Equiv.swap_apply_left] at h1
      exact haj h1
    · exfalso
      rw [h] at hstab
      obtain ⟨a, haj, -⟩ := exists_third j j
      obtain ⟨σ, hσ, hσj⟩ := exists_even_map j a
      have h1 := (hstab σ).mp ((stdAct_zero σ).2.1.mpr hσ)
      rw [hσj] at h1
      exact haj h1
    · refine ⟨h, ?_⟩
      rw [h] at hstab
      by_contra hj0
      obtain ⟨τ, hτ0, -, hmove⟩ := exists_swap_fixing 0
      exact hmove j hj0 ((hstab τ).mp ((stdAct_zero τ).2.2.1.mpr hτ0))
    · exfalso
      rw [h] at hstab
      obtain ⟨τ, hτj, hsign, -⟩ := exists_swap_fixing j
      have h1 : τ = 1 := (stdAct_zero τ).2.2.2.mp ((hstab τ).mpr hτj)
      rw [h1, map_one] at hsign
      exact absurd hsign (by decide)
  obtain ⟨hsize3, rfl⟩ := hsize
  refine ⟨hsize3, ?_⟩
  -- the other vertices of the part are the translates of the first one
  have hall : ∀ (i : Nat) (h : Vertex.aux p i ∈ C.U.vertices),
      ∃ σ : Equiv.Perm (Fin 3),
        e ⟨.aux p i, h⟩ = tridentGadget.ρ σ (e ⟨.aux p 0, h0⟩) ∧ σ 0 = idx i := by
    intro i h
    have hi : i < 3 := by
      have h1 := (C.aux_mem h).2
      rwa [hsize3] at h1
    obtain ⟨σ, hσ⟩ := exists_perm_map 0 (⟨i, hi⟩ : Fin 3)
    refine ⟨σ, ?_, by rw [hσ, idx_of_lt hi]⟩
    rw [← iso_trident_equivariant C.gadget e he σ ⟨.aux p 0, h0⟩]
    congr 1
    apply Subtype.ext
    rw [hval σ 0 h0, hsize3]
    show Vertex.aux p i = Vertex.aux p (app (toTable σ) (0 : Fin 3).val)
    rw [app_toTable, hσ]
  rcases hj with hj | hj
  · left
    intro i h
    obtain ⟨σ, h1, h2⟩ := hall i h
    rw [h1, hj]
    show TV.p (σ 0) = TV.p (idx i)
    rw [h2]
  · right
    intro i h
    obtain ⟨σ, h1, h2⟩ := hall i h
    rw [h1, hj]
    show TV.u (σ 0) = TV.u (idx i)
    rw [h2]

/-- With the composition `[3, 3]`, the isomorphism onto the trident is
    given by its values on the two parts. -/
theorem iso_eq_map (hC : C.parts = [3, 3]) (e : C.gadget.G ≃g trident)
    (he : (∀ i, e (C.gadget.lit i) = TV.x i) ∧ e C.gadget.gT = TV.gT ∧
      e C.gadget.gF = TV.gF ∧ e C.gadget.gB = TV.gB)
    (ψ : Vertex → TV) (hlit : ∀ i : Fin 3, ψ (.lit i.val) = TV.x i)
    (h0 : ∀ i (h : Vertex.aux 0 i ∈ C.U.vertices), e ⟨.aux 0 i, h⟩ = ψ (.aux 0 i))
    (h1 : ∀ i (h : Vertex.aux 1 i ∈ C.U.vertices), e ⟨.aux 1 i, h⟩ = ψ (.aux 1 i))
    (hT : ψ (.aux 2 0) = TV.gT) (hF : ψ (.aux 3 0) = TV.gF) (hB : ψ (.aux 4 0) = TV.gB) :
    ∀ v (h : v ∈ C.U.vertices), e ⟨v, h⟩ = ψ v := by
  have hlen : C.parts.length = 2 := by rw [hC]; rfl
  have hanchor : ∀ (d : Fin 3) (q j : Nat), q = 2 + d.val →
      ∀ h : Vertex.aux q j ∈ C.U.vertices, j = 0 ∧ (⟨.aux q j, h⟩ : C.Vert) = C.anchorV d := by
    intro d q j hq h
    subst hq
    have hs : C.U.size (2 + d.val) = 1 := by
      have h1 := attach_size C.parts d.isLt
      rwa [hlen] at h1
    have hj : j = 0 := by
      have h1 := (C.aux_mem h).2
      omega
    subst hj
    refine ⟨rfl, Subtype.ext ?_⟩
    show Vertex.aux (2 + d.val) 0 = Vertex.aux (C.parts.length + d.val) 0
    rw [hlen]
  intro v h
  rcases mem_vertices.mp h with ⟨i, hi, rfl⟩ | ⟨p, j, hp, _, rfl⟩
  · exact (he.1 ⟨i, hi⟩).trans (hlit ⟨i, hi⟩).symm
  · have hp5 : p < 5 := by
      have h1 : C.U.parts.length = C.parts.length + 3 := by
        show (C.parts ++ [1, 1, 1]).length = _
        rw [List.length_append]
        rfl
      omega
    interval_cases p
    · exact h0 j h
    · exact h1 j h
    · obtain ⟨hj, h2⟩ := hanchor 0 2 j rfl h
      subst hj
      rw [h2]
      exact he.2.1.trans hT.symm
    · obtain ⟨hj, h2⟩ := hanchor 1 3 j rfl h
      subst hj
      rw [h2]
      exact he.2.2.1.trans hF.symm
    · obtain ⟨hj, h2⟩ := hanchor 2 4 j rfl h
      subst hj
      rw [h2]
      exact he.2.2.2.trans hB.symm

/-- If the isomorphism onto the trident is the map `ψ` and `ψ` matches the
    edge list `T` with the edges of the trident, the candidate has the edge
    set `T`. -/
theorem edges_eq_of_map (e : C.gadget.G ≃g trident) (ψ : Vertex → TV) (T : List Edge)
    (hψ : ∀ v (h : v ∈ C.U.vertices), e ⟨v, h⟩ = ψ v) (hT : ∀ x ∈ T, x ∈ C.U.edges)
    (hadj : ∀ a ∈ C.U.vertices, ∀ b ∈ C.U.vertices,
      (normEdge (a, b) ∈ T ↔ trident.Adj (ψ a) (ψ b))) :
    ∀ x, x ∈ C.edges ↔ x ∈ T := by
  intro x
  constructor
  · intro hx
    obtain ⟨h1, h2, hn⟩ := mem_edges (C.sym.1 _ hx)
    have hadjC : C.gadget.G.Adj ⟨x.1, h1⟩ ⟨x.2, h2⟩ := C.adj_iff.mpr (by
      show normEdge x ∈ C.edges
      rw [hn]
      exact hx)
    have ht := e.map_rel_iff.mpr hadjC
    rw [hψ, hψ] at ht
    have h3 : normEdge x ∈ T := (hadj _ h1 _ h2).mpr ht
    rwa [hn] at h3
  · intro hx
    obtain ⟨h1, h2, hn⟩ := mem_edges (hT _ hx)
    have ht : trident.Adj (ψ x.1) (ψ x.2) := (hadj _ h1 _ h2).mp (by
      show normEdge x ∈ T
      rw [hn]
      exact hx)
    rw [← hψ _ h1, ← hψ _ h2] at ht
    have h3 : normEdge x ∈ C.edges := C.adj_iff.mp (e.map_rel_iff.mp ht)
    rwa [hn] at h3

end Candidate

end Def1

namespace Atlas

open Def1

/-- No S3-symmetric candidate with at most five auxiliary vertices passes
    the judge: the candidate is a gadget of Definition 1, and Theorem 16
    gives it at least six auxiliary vertices. -/
theorem no_symmetric_gadget_below_six :
    ∀ k, k ≤ 5 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      Statement.SymCandidate parts g → gadgetK threeColoring parts g false = none := by
  intro k hk parts hparts g hsym
  obtain ⟨hsum, hlegal, -⟩ := (Statement.compositions_are_all_orbit_compositions k parts).mp hparts
  cases hK : gadgetK threeColoring parts g false with
  | none => rfl
  | some b =>
    exfalso
    have hb : b = 1 := ((Statement.gadgetK_is_validity parts g b).1.mp hK).1
    subst hb
    have hv : (⟨parts, g, hlegal, hsym⟩ : Candidate).gadget.Valid :=
      (Candidate.valid_iff _).mpr hK
    classical
    have : Fintype (⟨parts, g, hlegal, hsym⟩ : Candidate).Vert := Fintype.ofFinite _
    have h6 := (minimum_unique _ hv).1
    rw [Candidate.card_aux] at h6
    have h7 : 6 ≤ parts.sum := h6
    omega

/-- Every S3-symmetric candidate with at most six auxiliary vertices that
    passes the judge has composition `[3, 3]` and the edge set of the
    trident, under one of its two labelings. -/
theorem trident_minimum_unique :
    ∀ k, k ≤ 6 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      Statement.SymCandidate parts g →
      ∀ b, gadgetK threeColoring parts g false = some b →
        parts = [3, 3] ∧ b = 1 ∧
          ((∀ e, e ∈ g ↔ e ∈ tridentA) ∨ (∀ e, e ∈ g ↔ e ∈ tridentB)) := by
  intro k hk parts hparts g hsym b hK
  obtain ⟨hsum, hlegal, -⟩ := (Statement.compositions_are_all_orbit_compositions k parts).mp hparts
  have hb : b = 1 := ((Statement.gadgetK_is_validity parts g b).1.mp hK).1
  subst hb
  -- the candidate as a gadget of Definition 1
  obtain ⟨C, hCp, hCe⟩ : ∃ C : Candidate, C.parts = parts ∧ C.edges = g :=
    ⟨⟨parts, g, hlegal, hsym⟩, rfl, rfl⟩
  have hv : C.gadget.Valid := C.valid_iff.mpr (by rw [hCp, hCe]; exact hK)
  classical
  have : Fintype C.Vert := Fintype.ofFinite _
  obtain ⟨h6, -, hiso⟩ := minimum_unique C.gadget hv
  have hcard := C.card_aux
  rw [hCp, hsum] at hcard
  obtain ⟨e, he⟩ := hiso (by omega)
  -- every part has size 3, so the composition is [3, 3]
  have hthree : ∀ x ∈ C.parts, x = 3 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [← C.size_eq hp]
    exact (C.part_of_trident e he hp).1
  have hC33 : C.parts = [3, 3] :=
    eq_three_three C.parts hthree (by rw [hCp, hsum]; omega)
  have hU : C.U = (threeColoring.attach [3, 3]).1 := by
    show (threeColoring.attach C.parts).1 = _
    rw [hC33]
  -- the two parts go to the branch layer and to the upper triangle
  obtain ⟨-, k0⟩ := C.part_of_trident e he (p := 0) (by rw [hC33]; decide)
  obtain ⟨-, k1⟩ := C.part_of_trident e he (p := 1) (by rw [hC33]; decide)
  have h00 : Vertex.aux 0 0 ∈ C.U.vertices := by rw [hU]; decide
  have h10 : Vertex.aux 1 0 ∈ C.U.vertices := by rw [hU]; decide
  have hne : (⟨.aux 0 0, h00⟩ : C.Vert) ≠ ⟨.aux 1 0, h10⟩ := fun h =>
    absurd (Vertex.aux.inj (congrArg Subtype.val h)).1 (by decide)
  refine ⟨hCp ▸ hC33, rfl, ?_⟩
  rw [← hCe]
  rcases k0 with k0 | k0 <;> rcases k1 with k1 | k1
  · exact absurd (e.injective ((k0 0 h00).trans (k1 0 h10).symm)) hne
  · left
    refine C.edges_eq_of_map e toTVA tridentA
      (C.iso_eq_map hC33 e he toTVA (fun i => congrArg TV.x (idx_val i)) k0 k1 rfl rfl rfl)
      (fun x hx => by rw [hU]; exact Statement.tridentA_tridentB_symmetric.1.1 x hx)
      (fun a ha b hb => toTVA_adj a (by rw [← hU]; exact ha) b (by rw [← hU]; exact hb))
  · right
    refine C.edges_eq_of_map e toTVB tridentB
      (C.iso_eq_map hC33 e he toTVB (fun i => congrArg TV.x (idx_val i)) k0 k1 rfl rfl rfl)
      (fun x hx => by rw [hU]; exact Statement.tridentA_tridentB_symmetric.2.1 x hx)
      (fun a ha b hb => toTVB_adj a (by rw [← hU]; exact ha) b (by rw [← hU]; exact hb))
  · exact absurd (e.injective ((k0 0 h00).trans (k1 0 h10).symm)) hne

end Atlas
