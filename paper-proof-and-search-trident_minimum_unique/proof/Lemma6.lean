import proof.Basics
import proof.OrbitStructure

/-!
  # Lemma 6 (orbit structure) for gadgets

  `OrbitStructure.lean` proves the group-theoretic part of Lemma 6: an orbit
  of an S3 action has size 1, 2, 3 or 6 and carries the trivial, sign,
  natural or free action. This file applies it to the vertices of a gadget
  (`stab_cases`) and proves the statements of Lemma 6 about edges. `lemma6`
  at the end of the file puts the parts together.

  * A size-3 orbit is a `Layer`: its vertices `pt 0`, `pt 1`, `pt 2` are
    permuted like the indices. Its induced subgraph is a triangle or three
    isolated vertices (`Layer.adj_self`).
  * A vertex of a size-1 or size-2 orbit is fixed by every even permutation,
    and it is adjacent to all three literals or to none
    (`adj_lit_of_even_fixed`). The two vertices of a size-2 orbit are swapped
    by every odd permutation (`sign_orbit`).
  * The literal attachment of a layer is empty, matched, crossed or both
    (`Layer.adj_lit`, with the two flags `matched` and `crossed`).

  The same symmetry argument describes the edges from a layer to an anchor
  (`Layer.adj_anchor`), to a vertex fixed by the even permutations
  (`Layer.adj_fixed`) and to another layer (`Layer.adj_layer`).
-/

namespace Def1

variable {V : Type}

-- --------------------------------------------- permutations of three points

theorem exists_third : ∀ a b : Fin 3, ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide

/-- Three pairwise different indices are all the indices. -/
theorem index_mem_of_three : ∀ x y z d : Fin 3,
    x ≠ y → x ≠ z → y ≠ z → d = x ∨ d = y ∨ d = z := by decide

theorem exists_perm_map (i j : Fin 3) : ∃ σ : Equiv.Perm (Fin 3), σ i = j :=
  ⟨Equiv.swap i j, Equiv.swap_apply_left i j⟩

/-- S3 moves any ordered pair of different indices to any other. -/
theorem exists_perm_pair {i j : Fin 3} (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
  have hj' : Equiv.swap 0 i j ≠ 0 := by
    intro h0
    have h1 := congrArg (Equiv.swap 0 i) h0
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h1
    exact h h1.symm
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hj'),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- The even permutations move any index to any other. -/
theorem exists_even_map (i j : Fin 3) :
    ∃ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 ∧ σ i = j := by
  by_cases hij : i = j
  · exact ⟨1, map_one _, hij⟩
  · obtain ⟨c, hci, hcj⟩ := exists_third i j
    refine ⟨Equiv.swap i j * Equiv.swap j c, ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap (Ne.symm hcj)]
      rfl
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hci),
        Equiv.swap_apply_left]

/-- The transposition that fixes `k` is odd and moves the other two indices. -/
theorem exists_swap_fixing (k : Fin 3) :
    ∃ τ : Equiv.Perm (Fin 3), τ k = k ∧ Equiv.Perm.sign τ = -1 ∧ ∀ i, i ≠ k → τ i ≠ i := by
  obtain ⟨a, hak, -⟩ := exists_third k k
  obtain ⟨b, hbk, hba⟩ := exists_third k a
  refine ⟨Equiv.swap a b, Equiv.swap_apply_of_ne_of_ne (Ne.symm hak) (Ne.symm hbk),
    Equiv.Perm.sign_swap (Ne.symm hba), fun i hik => ?_⟩
  rcases index_mem_of_three k a b i (Ne.symm hak) (Ne.symm hbk) (Ne.symm hba) with h | h | h
  · exact absurd h hik
  · rw [h, Equiv.swap_apply_left]
    exact hba
  · rw [h, Equiv.swap_apply_right]
    exact Ne.symm hba

/-- A relation on the indices that is invariant under S3 is given by its
    value on the diagonal and its value off the diagonal. -/
theorem rel_of_invariant {r : Fin 3 → Fin 3 → Prop}
    (h : ∀ (σ : Equiv.Perm (Fin 3)) (i j : Fin 3), r (σ i) (σ j) ↔ r i j) (i j : Fin 3) :
    r i j ↔ if i = j then r 0 0 else r 0 1 := by
  by_cases hij : i = j
  · rw [if_pos hij, ← hij]
    obtain ⟨σ, hσ⟩ := exists_perm_map 0 i
    have h1 := h σ 0 0
    rwa [hσ] at h1
  · rw [if_neg hij]
    obtain ⟨σ, h0, h1⟩ := exists_perm_pair hij
    have h2 := h σ 0 1
    rwa [h0, h1] at h2

/-- A property of the indices that is invariant under the even permutations
    holds for all indices or for none. -/
theorem pred_of_even_invariant {r : Fin 3 → Prop}
    (h : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → ∀ i, r (σ i) ↔ r i)
    (i j : Fin 3) : r i ↔ r j := by
  obtain ⟨σ, hσ, hij⟩ := exists_even_map i j
  have h1 := h σ hσ i
  rw [hij] at h1
  exact h1.symm

namespace Gadget

variable (g : Gadget V)

-- ------------------------------------------------- the stabilizer of a vertex

/-- The action of S3 on the vertices of a gadget. -/
@[reducible] def mulAction : MulAction (Equiv.Perm (Fin 3)) V where
  smul σ v := g.ρ σ v
  one_smul v := g.ρ_one v
  mul_smul σ τ v := g.ρ_mul σ τ v

/-- Lemma 6, orbit types, for a vertex `v` of a gadget. Its orbit has size 1,
    2, 3 or 6, and correspondingly: every permutation fixes `v`; exactly the
    even permutations fix `v` (sign action); for some index `k`, exactly the
    permutations fixing `k` fix `v` (natural action); only the identity
    fixes `v` (free orbit). -/
theorem stab_cases (v : V) :
    (∀ σ, g.ρ σ v = v) ∨
    (∀ σ, g.ρ σ v = v ↔ Equiv.Perm.sign σ = 1) ∨
    (∃ k : Fin 3, ∀ σ, g.ρ σ v = v ↔ σ k = k) ∨
    (∀ σ, g.ρ σ v = v ↔ σ = 1) := by
  let _ : MulAction (Equiv.Perm (Fin 3)) V := g.mulAction
  rcases orbit_structure v with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A vertex of a size-1 or size-2 orbit is adjacent to all three literals
    or to none: the even permutations fix it and move any literal to any
    other. -/
theorem adj_lit_of_even_fixed {w : V}
    (hw : ∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ w = w) (i j : Fin 3) :
    g.G.Adj w (g.lit i) ↔ g.G.Adj w (g.lit j) := by
  refine pred_of_even_invariant (r := fun i => g.G.Adj w (g.lit i)) (fun σ hσ i => ?_) i j
  show g.G.Adj w (g.lit (σ i)) ↔ g.G.Adj w (g.lit i)
  have h := g.adj_ρ σ (u := w) (v := g.lit i)
  rwa [hw σ hσ, g.ρ_lit] at h

/-- Lemma 6, a size-2 orbit: its two vertices `x` and `g.ρ τ x`, for any odd
    `τ`, are fixed by every even permutation and swapped by every odd
    permutation. -/
theorem sign_orbit {x : V} (hx : ∀ σ, g.ρ σ x = x ↔ Equiv.Perm.sign σ = 1)
    {τ : Equiv.Perm (Fin 3)} (hτ : Equiv.Perm.sign τ = -1) :
    g.ρ τ x ≠ x ∧
    (∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ x = x ∧ g.ρ σ (g.ρ τ x) = g.ρ τ x) ∧
    (∀ σ, Equiv.Perm.sign σ = -1 → g.ρ σ x = g.ρ τ x ∧ g.ρ σ (g.ρ τ x) = x) := by
  refine ⟨fun h => ?_, fun σ hσ => ⟨(hx σ).mpr hσ, ?_⟩, fun σ hσ => ⟨?_, ?_⟩⟩
  · have h1 := (hx τ).mp h
    rw [hτ] at h1
    exact absurd h1 (by decide)
  · rw [← g.ρ_mul, g.ρ_eq_ρ_iff, hx, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_inv, hσ, hτ]
    decide
  · rw [g.ρ_eq_ρ_iff, hx, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, hσ, hτ]
    decide
  · rw [← g.ρ_mul, hx, Equiv.Perm.sign_mul, hσ, hτ]
    decide

-- ------------------------------------------------------------------ layers

/-- A size-3 orbit with the natural action: `pt i` is its vertex with index
    `i`, and `g.ρ σ` moves `pt i` to `pt (σ i)`. -/
structure Layer (g : Gadget V) where
  pt : Fin 3 → V
  map : ∀ (σ : Equiv.Perm (Fin 3)) (i : Fin 3), g.ρ σ (pt i) = pt (σ i)
  inj : Function.Injective pt
  aux : ∀ i, g.IsAux (pt i)

/-- An auxiliary vertex `v` that is fixed exactly by the permutations fixing
    the index `k` lies in a layer, with index `k`. -/
noncomputable def Layer.ofNatural {v : V} {k : Fin 3} (hv : g.IsAux v)
    (hs : ∀ σ, g.ρ σ v = v ↔ σ k = k) : g.Layer where
  pt i := g.ρ (Equiv.swap k i) v
  map σ i := by
    rw [← g.ρ_mul, g.ρ_eq_ρ_iff, hs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_left, Equiv.swap_inv, Equiv.swap_apply_right]
  inj i j h := by
    rw [g.ρ_eq_ρ_iff, hs, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_inv] at h
    have h1 := congrArg (Equiv.swap k j) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h1
  aux i := g.isAux_map _ hv

theorem Layer.ofNatural_pt {v : V} {k : Fin 3} (hv : g.IsAux v)
    (hs : ∀ σ, g.ρ σ v = v ↔ σ k = k) : (Layer.ofNatural g hv hs).pt k = v := by
  show g.ρ (Equiv.swap k k) v = v
  rw [Equiv.swap_self]
  exact g.ρ_one v

variable {g}

namespace Layer

variable (L : g.Layer)

theorem pt_ne_lit (i j : Fin 3) : L.pt i ≠ g.lit j := (L.aux i).ne_lit j

theorem pt_ne_anchor (i t : Fin 3) : L.pt i ≠ g.anchor t := (L.aux i).ne_anchor t

/-- The literal attachment is matched: `pt i` is adjacent to `lit i`. -/
def matched : Prop := g.G.Adj (L.pt 0) (g.lit 0)

/-- The literal attachment is crossed: `pt i` is adjacent to the two
    literals `lit j` with `j ≠ i`. -/
def crossed : Prop := g.G.Adj (L.pt 0) (g.lit 1)

/-- Lemma 6, literal attachments of a size-3 orbit: empty, matched, crossed
    or both. -/
theorem adj_lit (i j : Fin 3) :
    g.G.Adj (L.pt i) (g.lit j) ↔ if i = j then L.matched else L.crossed := by
  refine rel_of_invariant (r := fun i j => g.G.Adj (L.pt i) (g.lit j)) (fun σ i j => ?_) i j
  show g.G.Adj (L.pt (σ i)) (g.lit (σ j)) ↔ g.G.Adj (L.pt i) (g.lit j)
  rw [← L.map σ i, ← g.ρ_lit σ j]
  exact g.adj_ρ σ

/-- The layer induces a triangle. -/
def triangle : Prop := g.G.Adj (L.pt 0) (L.pt 1)

/-- Lemma 6, induced subgraph of a size-3 orbit: a triangle or three
    isolated vertices. -/
theorem adj_self (i j : Fin 3) : g.G.Adj (L.pt i) (L.pt j) ↔ i ≠ j ∧ L.triangle := by
  have h := rel_of_invariant (r := fun i j => g.G.Adj (L.pt i) (L.pt j)) (fun σ i j => by
    show g.G.Adj (L.pt (σ i)) (L.pt (σ j)) ↔ g.G.Adj (L.pt i) (L.pt j)
    rw [← L.map σ i, ← L.map σ j]
    exact g.adj_ρ σ) i j
  rw [h]
  by_cases hij : i = j
  · rw [if_pos hij]
    constructor
    · intro h0
      exact absurd h0 (g.G.irrefl)
    · rintro ⟨h0, -⟩
      exact absurd hij h0
  · rw [if_neg hij]
    exact ⟨fun h0 => ⟨hij, h0⟩, fun h0 => h0.2⟩

/-- The layer is attached to the anchor `t`. -/
def anch (t : Fin 3) : Prop := g.G.Adj (L.pt 0) (g.anchor t)

/-- A vertex fixed by every even permutation is adjacent to all vertices of
    a layer or to none. -/
theorem adj_fixed {w : V} (hw : ∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ w = w) (i j : Fin 3) :
    g.G.Adj (L.pt i) w ↔ g.G.Adj (L.pt j) w := by
  refine pred_of_even_invariant (r := fun i => g.G.Adj (L.pt i) w) (fun σ hσ i => ?_) i j
  show g.G.Adj (L.pt (σ i)) w ↔ g.G.Adj (L.pt i) w
  have h := g.adj_ρ σ (u := L.pt i) (v := w)
  rwa [L.map, hw σ hσ] at h

/-- An anchor is adjacent to all vertices of a layer or to none. -/
theorem adj_anchor (i t : Fin 3) : g.G.Adj (L.pt i) (g.anchor t) ↔ L.anch t :=
  L.adj_fixed (fun σ _ => g.ρ_anchor' σ t) i 0

/-- The wiring between two layers is matched: `L.pt i` is adjacent to
    `U.pt i`. -/
def wm (U : g.Layer) : Prop := g.G.Adj (L.pt 0) (U.pt 0)

/-- The wiring between two layers is crossed: `L.pt i` is adjacent to
    `U.pt j` for `j ≠ i`. -/
def wc (U : g.Layer) : Prop := g.G.Adj (L.pt 0) (U.pt 1)

/-- The invariant wirings between two size-3 orbits: none, a matching, its
    complement, or both. -/
theorem adj_layer (U : g.Layer) (i j : Fin 3) :
    g.G.Adj (L.pt i) (U.pt j) ↔ if i = j then L.wm U else L.wc U := by
  refine rel_of_invariant (r := fun i j => g.G.Adj (L.pt i) (U.pt j)) (fun σ i j => ?_) i j
  show g.G.Adj (L.pt (σ i)) (U.pt (σ j)) ↔ g.G.Adj (L.pt i) (U.pt j)
  rw [← L.map σ i, ← U.map σ j]
  exact g.adj_ρ σ

/-- A vertex outside a layer is not moved into it. -/
theorem not_mem_map {w : V} (hw : ∀ i, L.pt i ≠ w) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    L.pt i ≠ g.ρ σ w := by
  intro h
  have h1 := congrArg (g.ρ σ⁻¹) h
  rw [g.ρ_inv_ρ, L.map] at h1
  exact hw _ h1

/-- Two layers are disjoint as soon as one vertex of the second is outside
    the first. -/
theorem disjoint_of_not_mem (U : g.Layer) {j0 : Fin 3} (h : ∀ i, L.pt i ≠ U.pt j0)
    (i j : Fin 3) : L.pt i ≠ U.pt j := by
  obtain ⟨σ, hσ⟩ := exists_perm_map j0 j
  have h1 := L.not_mem_map h σ i
  rwa [U.map, hσ] at h1

end Layer

-- ------------------------------------------------------------- the lemma

/-- Lemma 6 (orbit structure), for an auxiliary vertex `v` of a gadget. The
    orbit of `v` is the set of the vertices `g.ρ σ v`. One of the following
    holds.
    1. The orbit has size 1: every permutation fixes `v`. The vertex `v` is
       adjacent to all three literals or to none.
    2. The orbit has size 2 and carries the sign action: its two vertices
       `v` and `b` are fixed by every even permutation and swapped by every
       odd permutation. The vertex `v` is adjacent to all three literals or
       to none.
    3. The orbit has size 3 and carries the natural action: `v` is a vertex
       of a layer `L`. The subgraph induced on `L` is a triangle or three
       isolated vertices. The literal attachment of `L` is empty, matched
       (edges from `L.pt i` to `lit i`), crossed (edges from `L.pt i` to
       `lit j` for `j ≠ i`) or both.
    4. The orbit has size 6 and is free: only the identity fixes `v`. -/
theorem lemma6 (g : Gadget V) {v : V} (hv : g.IsAux v) :
    (Nat.card {w // ∃ σ, g.ρ σ v = w} = 1 ∧ (∀ σ, g.ρ σ v = v) ∧
      ((∀ i, g.G.Adj v (g.lit i)) ∨ ∀ i, ¬ g.G.Adj v (g.lit i))) ∨
    (Nat.card {w // ∃ σ, g.ρ σ v = w} = 2 ∧
      (∃ b, b ≠ v ∧ (∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ v = v ∧ g.ρ σ b = b) ∧
        ∀ σ, Equiv.Perm.sign σ = -1 → g.ρ σ v = b ∧ g.ρ σ b = v) ∧
      ((∀ i, g.G.Adj v (g.lit i)) ∨ ∀ i, ¬ g.G.Adj v (g.lit i))) ∨
    (Nat.card {w // ∃ σ, g.ρ σ v = w} = 3 ∧ ∃ L : g.Layer, (∃ k, L.pt k = v) ∧
      ((∀ i j, i ≠ j → g.G.Adj (L.pt i) (L.pt j)) ∨ ∀ i j, ¬ g.G.Adj (L.pt i) (L.pt j)) ∧
      ∀ i j, g.G.Adj (L.pt i) (g.lit j) ↔ if i = j then L.matched else L.crossed) ∨
    (Nat.card {w // ∃ σ, g.ρ σ v = w} = 6 ∧ ∀ σ, g.ρ σ v = v ↔ σ = 1) := by
  -- a vertex fixed by the even permutations: all three literals or none
  have hall : ∀ w : V, (∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ w = w) →
      (∀ i, g.G.Adj w (g.lit i)) ∨ ∀ i, ¬ g.G.Adj w (g.lit i) := by
    intro w hw
    by_cases h0 : g.G.Adj w (g.lit 0)
    · exact Or.inl fun i => (g.adj_lit_of_even_fixed hw 0 i).mp h0
    · exact Or.inr fun i hi => h0 ((g.adj_lit_of_even_fixed hw i 0).mp hi)
  let _ : MulAction (Equiv.Perm (Fin 3)) V := g.mulAction
  have hcard : Nat.card (MulAction.orbit (Equiv.Perm (Fin 3)) v) =
      Nat.card {w // ∃ σ, g.ρ σ v = w} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => MulAction.mem_orbit_iff)
  rcases orbit_structure v with ⟨hc, h⟩ | ⟨hc, h⟩ | ⟨hc, k, h⟩ | ⟨hc, h⟩
  · exact Or.inl ⟨hcard.symm.trans hc, h, hall v fun σ _ => h σ⟩
  · have h' : ∀ σ, g.ρ σ v = v ↔ Equiv.Perm.sign σ = 1 := h
    obtain ⟨τ, -, hτ, -⟩ := exists_swap_fixing 0
    obtain ⟨hne, he, ho⟩ := g.sign_orbit h' hτ
    exact Or.inr (Or.inl ⟨hcard.symm.trans hc, ⟨g.ρ τ v, hne, he, ho⟩,
      hall v fun σ hσ => (h' σ).mpr hσ⟩)
  · have h' : ∀ σ, g.ρ σ v = v ↔ σ k = k := h
    refine Or.inr (Or.inr (Or.inl ⟨hcard.symm.trans hc, Layer.ofNatural g hv h',
      ⟨k, Layer.ofNatural_pt g hv h'⟩, ?_, fun i j => Layer.adj_lit _ i j⟩))
    by_cases htri : (Layer.ofNatural g hv h').triangle
    · exact Or.inl fun i j hij => (Layer.adj_self _ i j).mpr ⟨hij, htri⟩
    · exact Or.inr fun i j hij => htri ((Layer.adj_self _ i j).mp hij).2
  · exact Or.inr (Or.inr (Or.inr ⟨hcard.symm.trans hc, h⟩))

end Gadget

end Def1

-- The build fails if this result depends on an axiom other than the three
-- standard ones.
/--
info: 'Def1.Gadget.lemma6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.Gadget.lemma6
