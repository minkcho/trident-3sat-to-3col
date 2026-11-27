import proof.Corollary9
import proof.Lemma11

/-!
  # Lemma 15 (free orbit exclusion)

  A free orbit cannot be the sole auxiliary orbit of a minimum valid gadget.

  Proof, as in the paper. The six vertices have the same number of literal
  neighbors, which is one by Lemma 11. By Corollary 9(ii) the orbit is
  attached to at most one anchor, and by the color-swap symmetry this anchor
  is G_T or G_F. Without an internal edge, the whole orbit can be colored B
  under (F, F, F). Otherwise let `(u, w)` be an internal edge. With G_F, the
  input (T, T, T) forces every vertex of the orbit to B. With G_T, a
  satisfying input in which the literal neighbors of `u` and `w` are false
  forces `u` and `w` to B. In both cases a satisfying input is rejected.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable (g : Gadget V)

/-- Lemma 15 (free orbit exclusion). In a minimum valid gadget, the
    auxiliary vertices are not a single free orbit: `v` is a vertex that only
    the identity fixes, and every auxiliary vertex is `g.ρ σ v` for some
    `σ`. The proof uses that the orbit is the sole auxiliary orbit, not that
    it is free. -/
theorem lemma15 [Finite V] (hv : g.Valid) (hmin : g.IsMinimum) {v : V} (hvaux : g.IsAux v)
    (hsole : ∀ w, g.IsAux w → ∃ σ, g.ρ σ v = w) (_hfree : ∀ σ, g.ρ σ v = v ↔ σ = 1) :
    False := by
  have h0 := hv.noLitAnchor
  -- Lemma 11: every vertex of the orbit has exactly one literal neighbor
  obtain ⟨w, hwaux, k, hk⟩ := g.lemma11 hv
  obtain ⟨σ₀, rfl⟩ := hsole w hwaux
  have hlit : ∀ (σ : Equiv.Perm (Fin 3)) (j : Fin 3),
      g.G.Adj (g.ρ σ v) (g.lit j) ↔ j = σ (σ₀⁻¹ k) := by
    intro σ j
    have e1 : g.ρ (σ₀ * σ⁻¹) (g.ρ σ v) = g.ρ σ₀ v := by rw [g.ρ_mul, g.ρ_inv_ρ]
    have e2 : g.ρ (σ₀ * σ⁻¹) (g.lit j) = g.lit (σ₀ (σ⁻¹ j)) := by
      rw [g.ρ_lit]
      rfl
    have h1 := g.adj_ρ (σ₀ * σ⁻¹) (u := g.ρ σ v) (v := g.lit j)
    rw [e1, e2, hk] at h1
    rw [← h1]
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp
  -- anchor attachments are uniform across the orbit
  have hanch : ∀ (σ : Equiv.Perm (Fin 3)) (t : Fin 3),
      g.G.Adj (g.ρ σ v) (g.anchor t) ↔ g.G.Adj v (g.anchor t) := by
    intro σ t
    have h1 := g.adj_ρ σ (u := v) (v := g.anchor t)
    rwa [g.ρ_anchor'] at h1
  -- by the color-swap symmetry the orbit is attached to G_T or to G_F
  have hTF : g.G.Adj v (g.anchor 0) ∨ g.G.Adj v (g.anchor 1) := by
    by_contra hno
    obtain ⟨w, hw, hadj⟩ := g.cor9_i hv
    rcases g.vertex_cases w with ⟨i, rfl⟩ | ⟨t, rfl⟩ | hwaux'
    · rcases hadj with h | h
      · exact (h0 i).1 h.symm
      · exact (h0 i).2 h.symm
    · exact hw t rfl
    · obtain ⟨σ, rfl⟩ := hsole w hwaux'
      rcases hadj with h | h
      · exact hno (Or.inl ((hanch σ 0).mp h.symm))
      · exact hno (Or.inr ((hanch σ 1).mp h.symm))
  -- and, by Corollary 9(ii), not to G_B
  have hnB : ¬ g.G.Adj v (g.anchor 2) := by
    intro h2
    rcases hTF with h | h
    · exact g.cor9_ii hv hmin hvaux (s := 0) (t := 2) (by decide) h h2
    · exact g.cor9_ii hv hmin hvaux (s := 1) (t := 2) (by decide) h h2
  by_cases hint : ∃ σ τ : Equiv.Perm (Fin 3), g.G.Adj (g.ρ σ v) (g.ρ τ v)
  · obtain ⟨σ, τ, hedge⟩ := hint
    rcases hTF with hT | hF
    · -- G_T: an input in which the literal neighbors of the two ends are false
      obtain ⟨m, hm1, hm2⟩ := exists_third (σ (σ₀⁻¹ k)) (τ (σ₀⁻¹ k))
      obtain ⟨c, hc⟩ := hv.of_true
        (α := fun i => decide (i ≠ σ (σ₀⁻¹ k) ∧ i ≠ τ (σ₀⁻¹ k))) (i := m)
        (decide_eq_true ⟨hm1, hm2⟩)
      have hB : ∀ π : Equiv.Perm (Fin 3), π = σ ∨ π = τ → c (g.ρ π v) = 2 := by
        intro π hπ
        refine eq_two_of_ne _ ?_ ?_
        · have h1 := hc.proper ((hanch π 0).mpr hT)
          rwa [hc.anchor] at h1
        · have h1 := hc.proper ((hlit π (π (σ₀⁻¹ k))).mpr rfl)
          have hfalse : decide (π (σ₀⁻¹ k) ≠ σ (σ₀⁻¹ k) ∧ π (σ₀⁻¹ k) ≠ τ (σ₀⁻¹ k)) = false := by
            rcases hπ with rfl | rfl
            · exact decide_eq_false (fun h => h.1 rfl)
            · exact decide_eq_false (fun h => h.2 rfl)
          rwa [hc.lit_false (i := π (σ₀⁻¹ k)) hfalse] at h1
      exact hc.proper hedge ((hB σ (Or.inl rfl)).trans (hB τ (Or.inr rfl)).symm)
    · -- G_F: (T, T, T) forces every vertex of the orbit to B
      obtain ⟨c, hc⟩ := hv.allTrue
      have hB : ∀ π : Equiv.Perm (Fin 3), c (g.ρ π v) = 2 := by
        intro π
        refine eq_two_of_ne _ ?_ ?_
        · have h1 := hc.proper ((hlit π (π (σ₀⁻¹ k))).mpr rfl)
          rwa [hc.lit_true (i := π (σ₀⁻¹ k)) rfl] at h1
        · have h1 := hc.proper ((hanch π 1).mpr hF)
          rwa [hc.anchor] at h1
      exact hc.proper hedge ((hB σ).trans (hB τ).symm)
  · -- no internal edge: color the whole orbit B under (F, F, F)
    have hA : ∀ t, recolor (recolor (fun _ => (2 : Fin 3)) g.lit fun _ => 1) g.anchor (fun t => t)
        (g.anchor t) = t := fun t => recolor_apply _ g.anchor_injective _ t
    have hLt : ∀ i, recolor (recolor (fun _ => (2 : Fin 3)) g.lit fun _ => 1) g.anchor (fun t => t)
        (g.lit i) = 1 := fun i =>
      (recolor_of_ne _ _ (fun t => (g.lit_ne_anchor' i t).symm)).trans
        (recolor_apply _ g.lit_inj _ i)
    have hX : ∀ w, g.IsAux w →
        recolor (recolor (fun _ => (2 : Fin 3)) g.lit fun _ => 1) g.anchor (fun t => t) w = 2 :=
      fun w hw => (recolor_of_ne _ _ (fun t => (hw.ne_anchor t).symm)).trans
        (recolor_of_ne _ _ (fun i => (hw.ne_lit i).symm))
    have hAX : ∀ (s : Fin 3) (w : V), g.IsAux w → g.G.Adj (g.anchor s) w → s ≠ 2 := by
      intro s w hw hadj hs
      obtain ⟨σ, rfl⟩ := hsole w hw
      rw [hs] at hadj
      exact hnB ((hanch σ 2).mp hadj.symm)
    refine hv.not_allFalse
      (c := recolor (recolor (fun _ => (2 : Fin 3)) g.lit fun _ => 1) g.anchor (fun t => t))
      (IsColoring.mk' ?_ hA (fun i => hLt i))
    intro u w huw
    rcases g.vertex_cases u with ⟨i, rfl⟩ | ⟨s, rfl⟩ | hu <;>
      rcases g.vertex_cases w with ⟨j, rfl⟩ | ⟨t, rfl⟩ | hw
    · exact absurd huw (g.lit_nonadj i j)
    · rw [hLt, hA, h0.eq_two huw]
      decide
    · rw [hLt, hX w hw]
      decide
    · rw [hA, hLt, h0.eq_two huw.symm]
      decide
    · rw [hA, hA]
      intro hst
      rw [hst] at huw
      exact g.G.irrefl huw
    · rw [hA, hX w hw]
      exact hAX s w hw huw
    · rw [hX u hu, hLt]
      decide
    · rw [hX u hu, hA]
      exact Ne.symm (hAX t u hu huw.symm)
    · obtain ⟨σ, rfl⟩ := hsole u hu
      obtain ⟨τ, rfl⟩ := hsole w hw
      exact absurd ⟨σ, τ, huw⟩ hint

end Gadget

end Def1
