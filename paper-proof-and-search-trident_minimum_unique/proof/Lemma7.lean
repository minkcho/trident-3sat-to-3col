import proof.Lemma6

/-!
  # Lemma 7 (size-2 orbit reduction)

  Suppose a gadget has exactly one size-2 auxiliary orbit `{a, b}` and all
  its other auxiliary orbits have size 1 or 3. Then `a` and `b` have the same
  neighbors outside `{a, b}`, and the graph carries an S3 action that agrees
  with the given one outside `{a, b}` and fixes `a` and `b`. Under the new
  action the size-2 orbit is two size-1 orbits.

  Proof, as in the paper. The alternating group fixes `a` and `b` and acts
  transitively on a size-3 orbit, so `a` and `b` each have an all-or-nothing
  connection to such an orbit. An odd permutation swaps `a` and `b`, so they
  have the same adjacencies to the fixed vertices and to the size-3 orbits.
  The new action is `ρ' σ = ρ σ` for even `σ` and `ρ' σ = τ ρ σ` for odd
  `σ`, where `τ` is the automorphism that swaps `a` and `b`.
-/

namespace Def1

variable {V : Type}

namespace Gadget

open Classical in
/-- The automorphism that swaps `a` and `b`, when the swap preserves
    adjacency. -/
noncomputable def swapIso (g : Gadget V) (a b : V)
    (h : ∀ u v, g.G.Adj (Equiv.swap a b u) (Equiv.swap a b v) ↔ g.G.Adj u v) :
    g.G ≃g g.G where
  toEquiv := Equiv.swap a b
  map_rel_iff' := h _ _

/-- The action twisted by an involution `τ` that commutes with it: an even
    permutation acts as before, an odd one is followed by `τ`. This is a
    group homomorphism because the sign is one. -/
noncomputable def twist (g : Gadget V) (τ : g.G ≃g g.G)
    (hcomm : ∀ σ, τ * g.ρ σ = g.ρ σ * τ) (hsq : τ * τ = 1) :
    Equiv.Perm (Fin 3) →* (g.G ≃g g.G) where
  toFun σ := if Equiv.Perm.sign σ = 1 then g.ρ σ else τ * g.ρ σ
  map_one' := by rw [if_pos (map_one _), map_one]
  map_mul' σ σ' := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ') with ht | ht
    · rw [if_pos (by rw [Equiv.Perm.sign_mul, hs, ht]; rfl), if_pos hs, if_pos ht, map_mul]
    · rw [if_neg (by rw [Equiv.Perm.sign_mul, hs, ht]; decide), if_pos hs,
        if_neg (by rw [ht]; decide), map_mul, ← mul_assoc, hcomm σ, mul_assoc]
    · rw [if_neg (by rw [Equiv.Perm.sign_mul, hs, ht]; decide),
        if_neg (by rw [hs]; decide), if_pos ht, map_mul, mul_assoc]
    · rw [if_pos (by rw [Equiv.Perm.sign_mul, hs, ht]; decide),
        if_neg (by rw [hs]; decide), if_neg (by rw [ht]; decide), map_mul]
      calc g.ρ σ * g.ρ σ' = τ * τ * (g.ρ σ * g.ρ σ') := by rw [hsq, one_mul]
        _ = τ * (τ * g.ρ σ) * g.ρ σ' := by simp only [mul_assoc]
        _ = τ * (g.ρ σ * τ) * g.ρ σ' := by rw [hcomm σ]
        _ = τ * g.ρ σ * (τ * g.ρ σ') := by simp only [mul_assoc]

theorem twist_even (g : Gadget V) (τ : g.G ≃g g.G)
    (hcomm : ∀ σ, τ * g.ρ σ = g.ρ σ * τ) (hsq : τ * τ = 1) {σ : Equiv.Perm (Fin 3)}
    (hs : Equiv.Perm.sign σ = 1) (v : V) : g.twist τ hcomm hsq σ v = g.ρ σ v := by
  show (if Equiv.Perm.sign σ = 1 then g.ρ σ else τ * g.ρ σ) v = g.ρ σ v
  rw [if_pos hs]

theorem twist_odd (g : Gadget V) (τ : g.G ≃g g.G)
    (hcomm : ∀ σ, τ * g.ρ σ = g.ρ σ * τ) (hsq : τ * τ = 1) {σ : Equiv.Perm (Fin 3)}
    (hs : Equiv.Perm.sign σ = -1) (v : V) : g.twist τ hcomm hsq σ v = τ (g.ρ σ v) := by
  show (if Equiv.Perm.sign σ = 1 then g.ρ σ else τ * g.ρ σ) v = τ (g.ρ σ v)
  rw [if_neg (by rw [hs]; decide)]
  rfl

/-- Lemma 7 (size-2 orbit reduction). Let `{a, b}` be a size-2 auxiliary
    orbit: the even permutations fix `a` and `b`, and the odd ones swap them.
    Let every other auxiliary vertex lie in an orbit of size 1 or 3. Then `a`
    and `b` have the same neighbors outside `{a, b}`, and there is a gadget
    `g'` with the same edges, literals and anchors, whose action fixes `a`
    and `b` and agrees with the action of `g` on all other vertices. -/
theorem lemma7 (g : Gadget V) {a b : V} (ha : g.IsAux a) (hb : g.IsAux b)
    (heven : ∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ a = a ∧ g.ρ σ b = b)
    (hodd : ∀ σ, Equiv.Perm.sign σ = -1 → g.ρ σ a = b ∧ g.ρ σ b = a)
    (hother : ∀ w, g.IsAux w → w ≠ a → w ≠ b →
      (∀ σ, g.ρ σ w = w) ∨ ∃ k : Fin 3, ∀ σ, g.ρ σ w = w ↔ σ k = k) :
    (∀ w, w ≠ a → w ≠ b → (g.G.Adj a w ↔ g.G.Adj b w)) ∧
    ∃ g' : Gadget V, (∀ u w, g'.G.Adj u w ↔ g.G.Adj u w) ∧ g'.lit = g.lit ∧
      g'.gT = g.gT ∧ g'.gF = g.gF ∧ g'.gB = g.gB ∧
      (∀ σ, g'.ρ σ a = a ∧ g'.ρ σ b = b) ∧
      ∀ σ w, w ≠ a → w ≠ b → g'.ρ σ w = g.ρ σ w := by
  classical
  -- A3 fixes b, so b has an all-or-nothing connection to a size-3 orbit
  have hbe : ∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ b = b := fun σ hσ => (heven σ hσ).2
  -- an odd permutation swaps a and b
  obtain ⟨τ₀, -, hτ₀, -⟩ := exists_swap_fixing 0
  -- identical external neighborhoods
  have hnb : ∀ w, w ≠ a → w ≠ b → (g.G.Adj a w ↔ g.G.Adj b w) := by
    intro w hwa hwb
    -- the odd permutation carries the pair (a, w) to (b, τ₀ w)
    have h1 : g.G.Adj a w ↔ g.G.Adj b (g.ρ τ₀ w) := by
      have h := g.adj_ρ τ₀ (u := a) (v := w)
      rw [(hodd τ₀ hτ₀).1] at h
      exact h.symm
    rw [h1]
    rcases g.vertex_cases w with ⟨i, rfl⟩ | ⟨t, rfl⟩ | hw
    · -- the literals: b is adjacent to all three or to none
      rw [g.ρ_lit]
      exact g.adj_lit_of_even_fixed hbe (τ₀ i) i
    · -- an anchor is fixed
      rw [g.ρ_anchor']
    · rcases hother w hw hwa hwb with h | ⟨k, h⟩
      · -- a singleton is fixed
        rw [h τ₀]
      · -- a size-3 orbit: b is adjacent to all its vertices or to none
        obtain ⟨L, hL⟩ : ∃ L : g.Layer, L.pt k = w := ⟨_, Layer.ofNatural_pt g hw h⟩
        rw [← hL, L.map]
        exact ⟨fun h2 => ((L.adj_fixed hbe (τ₀ k) k).mp h2.symm).symm,
          fun h2 => ((L.adj_fixed hbe k (τ₀ k)).mp h2.symm).symm⟩
  refine ⟨hnb, ?_⟩
  -- the swap of a and b preserves adjacency
  have hirr : ∀ x : V, ¬ g.G.Adj x x := fun x => g.G.irrefl
  have hsw : ∀ u v, g.G.Adj (Equiv.swap a b u) (Equiv.swap a b v) ↔ g.G.Adj u v := by
    intro u v
    by_cases hua : u = a
    · by_cases hva : v = a
      · rw [hua, hva]
        exact ⟨fun h => absurd h (hirr _), fun h => absurd h (hirr _)⟩
      · by_cases hvb : v = b
        · rw [hua, hvb, Equiv.swap_apply_left, Equiv.swap_apply_right]
          exact ⟨fun h => h.symm, fun h => h.symm⟩
        · rw [hua, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hva hvb]
          exact (hnb v hva hvb).symm
    · by_cases hub : u = b
      · by_cases hva : v = a
        · rw [hub, hva, Equiv.swap_apply_right, Equiv.swap_apply_left]
          exact ⟨fun h => h.symm, fun h => h.symm⟩
        · by_cases hvb : v = b
          · rw [hub, hvb]
            exact ⟨fun h => absurd h (hirr _), fun h => absurd h (hirr _)⟩
          · rw [hub, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hva hvb]
            exact hnb v hva hvb
      · rw [Equiv.swap_apply_of_ne_of_ne hua hub]
        have hu := hnb u hua hub
        by_cases hva : v = a
        · rw [hva, Equiv.swap_apply_left]
          exact ⟨fun h => (hu.mpr h.symm).symm, fun h => (hu.mp h.symm).symm⟩
        · by_cases hvb : v = b
          · rw [hvb, Equiv.swap_apply_right]
            exact ⟨fun h => (hu.mp h.symm).symm, fun h => (hu.mpr h.symm).symm⟩
          · rw [Equiv.swap_apply_of_ne_of_ne hva hvb]
  -- each permutation fixes a and b or swaps them
  have hset : ∀ σ : Equiv.Perm (Fin 3),
      (g.ρ σ a = a ∧ g.ρ σ b = b) ∨ (g.ρ σ a = b ∧ g.ρ σ b = a) := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · exact Or.inl (heven σ hs)
    · exact Or.inr (hodd σ hs)
  have hmove : ∀ (σ : Equiv.Perm (Fin 3)) (v : V), v ≠ a → v ≠ b →
      g.ρ σ v ≠ a ∧ g.ρ σ v ≠ b := by
    intro σ v hva hvb
    rcases hset σ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun h => hva (g.ρ_injective σ (h.trans h1.symm)),
        fun h => hvb (g.ρ_injective σ (h.trans h2.symm))⟩
    · exact ⟨fun h => hvb (g.ρ_injective σ (h.trans h2.symm)),
        fun h => hva (g.ρ_injective σ (h.trans h1.symm))⟩
  have hsq : g.swapIso a b hsw * g.swapIso a b hsw = 1 :=
    RelIso.ext fun v => Equiv.swap_apply_self a b v
  have hcomm : ∀ σ, g.swapIso a b hsw * g.ρ σ = g.ρ σ * g.swapIso a b hsw := by
    intro σ
    refine RelIso.ext fun v => ?_
    show Equiv.swap a b (g.ρ σ v) = g.ρ σ (Equiv.swap a b v)
    by_cases hva : v = a
    · rw [hva, Equiv.swap_apply_left]
      rcases hset σ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, Equiv.swap_apply_left]
      · rw [h1, h2, Equiv.swap_apply_right]
    · by_cases hvb : v = b
      · rw [hvb, Equiv.swap_apply_right]
        rcases hset σ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, Equiv.swap_apply_right]
        · rw [h1, h2, Equiv.swap_apply_left]
      · rw [Equiv.swap_apply_of_ne_of_ne hva hvb,
          Equiv.swap_apply_of_ne_of_ne (hmove σ v hva hvb).1 (hmove σ v hva hvb).2]
  -- the twisted action fixes a and b and agrees with ρ elsewhere
  have hval : ∀ (σ : Equiv.Perm (Fin 3)) (w : V), w ≠ a → w ≠ b →
      g.twist (g.swapIso a b hsw) hcomm hsq σ w = g.ρ σ w := by
    intro σ w hwa hwb
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · exact g.twist_even _ hcomm hsq hs w
    · rw [g.twist_odd _ hcomm hsq hs w]
      exact Equiv.swap_apply_of_ne_of_ne (hmove σ w hwa hwb).1 (hmove σ w hwa hwb).2
  have hab' : ∀ σ : Equiv.Perm (Fin 3),
      g.twist (g.swapIso a b hsw) hcomm hsq σ a = a ∧
      g.twist (g.swapIso a b hsw) hcomm hsq σ b = b := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [g.twist_even _ hcomm hsq hs, g.twist_even _ hcomm hsq hs]
      exact heven σ hs
    · rw [g.twist_odd _ hcomm hsq hs, g.twist_odd _ hcomm hsq hs, (hodd σ hs).1, (hodd σ hs).2]
      exact ⟨Equiv.swap_apply_right a b, Equiv.swap_apply_left a b⟩
  refine ⟨{ g with
    ρ := g.twist (g.swapIso a b hsw) hcomm hsq
    ρ_lit := fun σ i => ?_
    ρ_anchor := fun σ => ?_ }, fun _ _ => Iff.rfl, rfl, rfl, rfl, rfl, hab', hval⟩
  · rw [hval σ (g.lit i) (fun h => ha.ne_lit i h.symm) (fun h => hb.ne_lit i h.symm)]
    exact g.ρ_lit σ i
  · have hT := hval σ (g.anchor 0) (fun h => ha.ne_anchor 0 h.symm) (fun h => hb.ne_anchor 0 h.symm)
    have hF := hval σ (g.anchor 1) (fun h => ha.ne_anchor 1 h.symm) (fun h => hb.ne_anchor 1 h.symm)
    have hB := hval σ (g.anchor 2) (fun h => ha.ne_anchor 2 h.symm) (fun h => hb.ne_anchor 2 h.symm)
    exact ⟨hT.trans (g.ρ_anchor σ).1, hF.trans (g.ρ_anchor σ).2.1, hB.trans (g.ρ_anchor σ).2.2⟩

end Gadget

end Def1
