import proof.Theorem16

/-!
  # The remark after Theorem 16: the isomorphism is unique

  Theorem 16 gives an isomorphism onto the trident that fixes each literal
  and each anchor. The paper remarks three things about it.

  * Fixing each literal is the same as fixing the set of literals: if an
    isomorphism permutes the literals according to `π`, composing it with
    `ρ(π⁻¹)` gives one that fixes them (`iso_of_literal_set`).
  * An automorphism of the trident that fixes all literals and anchors is
    the identity: it fixes each `p_i`, the unique neighbor of `x_i` other
    than G_B, and then each `u_i`, the unique neighbor of `p_i` other than
    `x_i` and G_T (`trident_rigid`). So two isomorphisms that fix the
    literals and the anchors coincide (`iso_trident_unique`).
  * Hence the isomorphism commutes with the two S3-actions
    (`iso_trident_equivariant`).
-/

namespace Def1

variable {V : Type}

-- ------------------------------------------ neighbors in the trident (data)

theorem trident_adj_x_p : ∀ i : Fin 3, trident.Adj (TV.x i) (TV.p i) := by decide

theorem trident_adj_p_u : ∀ i : Fin 3, trident.Adj (TV.p i) (TV.u i) := by decide

/-- The neighbors of `x_i` are `p_i` and G_B. -/
theorem trident_nb_x : ∀ (i : Fin 3) (w : TV),
    trident.Adj (TV.x i) w → w = TV.p i ∨ w = TV.gB := by decide

/-- The neighbors of `p_i` are `x_i`, `u_i` and G_T. -/
theorem trident_nb_p : ∀ (i : Fin 3) (w : TV),
    trident.Adj (TV.p i) w → w = TV.x i ∨ w = TV.u i ∨ w = TV.gT := by decide

-- --------------------------------------------------------------- rigidity

/-- An automorphism of the trident that fixes each literal and each anchor
    is the identity. -/
theorem trident_rigid (f : trident ≃g trident) (hx : ∀ i, f (TV.x i) = TV.x i)
    (hT : f TV.gT = TV.gT) (hF : f TV.gF = TV.gF) (hB : f TV.gB = TV.gB) (v : TV) :
    f v = v := by
  -- `p_i` is the unique neighbor of `x_i` other than G_B
  have hp : ∀ i, f (TV.p i) = TV.p i := by
    intro i
    have h1 : trident.Adj (f (TV.x i)) (f (TV.p i)) := f.map_rel_iff.mpr (trident_adj_x_p i)
    rw [hx i] at h1
    rcases trident_nb_x i _ h1 with h | h
    · exact h
    · exact absurd (f.injective (h.trans hB.symm)) (by simp)
  -- `u_i` is the unique neighbor of `p_i` other than `x_i` and G_T
  have hu : ∀ i, f (TV.u i) = TV.u i := by
    intro i
    have h1 : trident.Adj (f (TV.p i)) (f (TV.u i)) := f.map_rel_iff.mpr (trident_adj_p_u i)
    rw [hp i] at h1
    rcases trident_nb_p i _ h1 with h | h | h
    · exact absurd (f.injective (h.trans (hx i).symm)) (by simp)
    · exact h
    · exact absurd (f.injective (h.trans hT.symm)) (by simp)
  cases v with
  | x i => exact hx i
  | p i => exact hp i
  | u i => exact hu i
  | gT => exact hT
  | gF => exact hF
  | gB => exact hB

-- -------------------------------------------------------------- uniqueness

/-- Two isomorphisms onto the trident that fix each literal and each anchor
    coincide. -/
theorem iso_trident_unique (g : Gadget V) (e e' : g.G ≃g trident)
    (he : (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB)
    (he' : (∀ i, e' (g.lit i) = TV.x i) ∧ e' g.gT = TV.gT ∧ e' g.gF = TV.gF ∧
      e' g.gB = TV.gB) (v : V) : e v = e' v := by
  -- `e' ∘ e⁻¹` is an automorphism of the trident that fixes literals and anchors
  have hs : ∀ w, e.symm (e w) = w := fun w => e.symm_apply_apply w
  have hx : ∀ i, e.symm (TV.x i) = g.lit i := fun i => by rw [← he.1 i, hs]
  have hT : e.symm TV.gT = g.gT := by rw [← he.2.1, hs]
  have hF : e.symm TV.gF = g.gF := by rw [← he.2.2.1, hs]
  have hB : e.symm TV.gB = g.gB := by rw [← he.2.2.2, hs]
  have h := trident_rigid (e.symm.trans e')
    (fun i => by
      show e' (e.symm (TV.x i)) = TV.x i
      rw [hx i, he'.1 i])
    (by
      show e' (e.symm TV.gT) = TV.gT
      rw [hT, he'.2.1])
    (by
      show e' (e.symm TV.gF) = TV.gF
      rw [hF, he'.2.2.1])
    (by
      show e' (e.symm TV.gB) = TV.gB
      rw [hB, he'.2.2.2])
    (e v)
  have h2 : e' (e.symm (e v)) = e v := h
  rw [hs] at h2
  exact h2.symm

/-- The isomorphism of Theorem 16 commutes with the two S3-actions. -/
theorem iso_trident_equivariant (g : Gadget V) (e : g.G ≃g trident)
    (he : (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB)
    (σ : Equiv.Perm (Fin 3)) (v : V) : e (g.ρ σ v) = tridentGadget.ρ σ (e v) := by
  have hs : ∀ w, (tridentGadget.ρ σ).symm (tridentGadget.ρ σ w) = w :=
    fun w => (tridentGadget.ρ σ).symm_apply_apply w
  have hback : ∀ w w', tridentGadget.ρ σ w = w' → (tridentGadget.ρ σ).symm w' = w :=
    fun w w' hw => by rw [← hw, hs]
  -- `ρ_T(σ)⁻¹ ∘ e ∘ ρ(σ)` also fixes the literals and the anchors
  have h := iso_trident_unique g e (((g.ρ σ).trans e).trans (tridentGadget.ρ σ).symm) he
    ⟨fun i => by
        show (tridentGadget.ρ σ).symm (e (g.ρ σ (g.lit i))) = TV.x i
        rw [g.ρ_lit, he.1]
        exact hback _ _ (tridentGadget.ρ_lit σ i),
     by
        show (tridentGadget.ρ σ).symm (e (g.ρ σ g.gT)) = TV.gT
        rw [(g.ρ_anchor σ).1, he.2.1]
        exact hback _ _ (tridentGadget.ρ_anchor σ).1,
     by
        show (tridentGadget.ρ σ).symm (e (g.ρ σ g.gF)) = TV.gF
        rw [(g.ρ_anchor σ).2.1, he.2.2.1]
        exact hback _ _ (tridentGadget.ρ_anchor σ).2.1,
     by
        show (tridentGadget.ρ σ).symm (e (g.ρ σ g.gB)) = TV.gB
        rw [(g.ρ_anchor σ).2.2, he.2.2.2]
        exact hback _ _ (tridentGadget.ρ_anchor σ).2.2⟩ v
  have h2 : e v = (tridentGadget.ρ σ).symm (e (g.ρ σ v)) := h
  rw [h2]
  exact ((tridentGadget.ρ σ).apply_symm_apply _).symm

/-- Fixing the set of literals is enough: an isomorphism onto the trident
    that fixes the anchors and permutes the literals according to `π` gives
    one that fixes each literal, by composing it with `ρ(π⁻¹)`. -/
theorem iso_of_literal_set (g : Gadget V) (e : g.G ≃g trident) (π : Equiv.Perm (Fin 3))
    (hlit : ∀ i, e (g.lit i) = TV.x (π i))
    (hT : e g.gT = TV.gT) (hF : e g.gF = TV.gF) (hB : e g.gB = TV.gB) :
    ∃ e' : g.G ≃g trident,
      (∀ i, e' (g.lit i) = TV.x i) ∧ e' g.gT = TV.gT ∧ e' g.gF = TV.gF ∧ e' g.gB = TV.gB := by
  refine ⟨(g.ρ π⁻¹).trans e, fun i => ?_, ?_, ?_, ?_⟩
  · show e (g.ρ π⁻¹ (g.lit i)) = TV.x i
    rw [g.ρ_lit, hlit]
    simp
  · show e (g.ρ π⁻¹ g.gT) = TV.gT
    rw [(g.ρ_anchor π⁻¹).1, hT]
  · show e (g.ρ π⁻¹ g.gF) = TV.gF
    rw [(g.ρ_anchor π⁻¹).2.1, hF]
  · show e (g.ρ π⁻¹ g.gB) = TV.gB
    rw [(g.ρ_anchor π⁻¹).2.2, hB]

end Def1
