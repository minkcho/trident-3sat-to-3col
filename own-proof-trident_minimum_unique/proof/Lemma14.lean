import proof.TwoLayers
import proof.Corollary9

/-!
  # Lemma 14

  No minimum valid gadget has exactly two size-3 auxiliary orbits that are
  both isolated layers.

  Proof, as in the paper. By Corollary 9(ii) each layer has at most one
  palette anchor. Under (F, F, F), color the two layers T and B, in either
  order. One order respects the anchors unless both layers are attached to
  G_T or both to G_B. The second case is excluded by Corollary 9(i). In the
  first case: without an edge between the layers, color both layers B; if a
  layer has no literal neighbor, color it F and the other B. Otherwise both
  layers are attached to the literals and to each other; under (F, F, T) two
  vertices of each layer see a false literal and G_T and have color B, and
  the wiring joins two of them.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable {g : Gadget V}

/-- A layer attached to G_T and to the literals: under (F, F, T) its
    vertices 0 and 1 see a false literal and G_T, so they have color B. -/
theorem Layer.forced_B (M : g.Layer) {c : V → Fin 3} (hc : g.IsColoring (onlyTrue 2) c)
    (hM0 : M.anch 0) (hMl : M.matched ∨ M.crossed) : c (M.pt 0) = 2 ∧ c (M.pt 1) = 2 := by
  have hx0 : c (g.lit 0) = 1 := hc.lit_false (by decide)
  have hx1 : c (g.lit 1) = 1 := hc.lit_false (by decide)
  have hT : ∀ i, c (M.pt i) ≠ 0 := by
    intro i
    have h1 := hc.proper ((M.adj_anchor i 0).mpr hM0)
    rwa [hc.anchor] at h1
  rcases hMl with hm | hcr
  · have a0 := hc.proper ((M.adj_lit 0 0).mpr (by rwa [if_pos rfl]))
    have a1 := hc.proper ((M.adj_lit 1 1).mpr (by rwa [if_pos rfl]))
    rw [hx0] at a0
    rw [hx1] at a1
    exact ⟨eq_two_of_ne _ (hT 0) a0, eq_two_of_ne _ (hT 1) a1⟩
  · have a0 := hc.proper ((M.adj_lit 0 1).mpr (by rwa [if_neg (by decide)]))
    have a1 := hc.proper ((M.adj_lit 1 0).mpr (by rwa [if_neg (by decide)]))
    rw [hx1] at a0
    rw [hx0] at a1
    exact ⟨eq_two_of_ne _ (hT 0) a0, eq_two_of_ne _ (hT 1) a1⟩

/-- A second size-3 orbit exhausts the six-vertex budget: in a minimum
    gadget, two disjoint size-3 orbits are all the auxiliary vertices. -/
theorem two_layers_exhaust_budget [Finite V] (hmin : g.IsMinimum) (L U : g.Layer)
    (hdisj : ∀ i j, L.pt i ≠ U.pt j) :
    Nat.card {v // g.IsAux v} = 6 ∧
      ∀ w, g.IsAux w → (∃ i, w = L.pt i) ∨ ∃ i, w = U.pt i := by
  have hk6 := hmin.card_le_six
  have hinj : Function.Injective (Sum.elim L.pt U.pt) := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · exact congrArg Sum.inl (L.inj hxy)
    · exact absurd hxy (hdisj i j)
    · exact absurd hxy.symm (hdisj j i)
    · exact congrArg Sum.inr (U.inj hxy)
  have haux : ∀ x, g.IsAux (Sum.elim L.pt U.pt x) := by
    rintro (i | i)
    · exact L.aux i
    · exact U.aux i
  have hc : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by
    rw [Fintype.card_sum, Fintype.card_fin]
  have hge := g.card_aux_ge _ hinj haux
  have hall := g.aux_surj _ hinj haux (by rw [hc]; exact hk6)
  refine ⟨by omega, fun w hw => ?_⟩
  obtain ⟨x, hx⟩ := hall w hw
  rcases x with i | i
  · exact Or.inl ⟨i, hx.symm⟩
  · exact Or.inr ⟨i, hx.symm⟩

/-- The argument of Lemma 14, for a gadget whose auxiliary vertices are two
    size-3 orbits. -/
theorem TwoLayers.not_both_isolated [Finite V] (T : g.TwoLayers) (hv : g.Valid)
    (hmin : g.IsMinimum) (hL : ¬ T.L.triangle) (hU : ¬ T.U.triangle) : False := by
  have h0 := hv.noLitAnchor
  -- Corollary 9(ii): each layer has at most one palette anchor
  have hLone : ∀ s t : Fin 3, s ≠ t → T.L.anch s → T.L.anch t → False :=
    fun s t hst hs ht => g.cor9_ii hv hmin (T.L.aux 0) hst hs ht
  have hUone : ∀ s t : Fin 3, s ≠ t → T.U.anch s → T.U.anch t → False :=
    fun s t hst hs ht => g.cor9_ii hv hmin (T.U.aux 0) hst hs ht
  -- under (F, F, F): L with T and U with B
  by_cases h1 : ¬ T.L.anch 0 ∧ ¬ T.U.anch 2
  · obtain ⟨c, hc⟩ := T.uniform_allFalse h0 hL hU 0 2 (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) h1.1 h1.2 (fun h => absurd h (by decide))
    exact hv.not_allFalse hc
  -- L with B and U with T
  by_cases h2 : ¬ T.L.anch 2 ∧ ¬ T.U.anch 0
  · obtain ⟨c, hc⟩ := T.uniform_allFalse h0 hL hU 2 0 (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) h2.1 h2.2 (fun h => absurd h (by decide))
    exact hv.not_allFalse hc
  -- neither order works: both layers have the anchor G_T, or both have G_B
  have hcases : (T.L.anch 0 ∧ T.U.anch 0) ∨ (T.L.anch 2 ∧ T.U.anch 2) := by
    by_cases hL0 : T.L.anch 0
    · by_cases hU0 : T.U.anch 0
      · exact Or.inl ⟨hL0, hU0⟩
      · exact absurd ⟨fun hL2 => hLone 0 2 (by decide) hL0 hL2, hU0⟩ h2
    · have hU2 : T.U.anch 2 := by
        by_contra hU2
        exact h1 ⟨hL0, hU2⟩
      by_cases hL2 : T.L.anch 2
      · exact Or.inr ⟨hL2, hU2⟩
      · exact absurd ⟨hL2, fun hU0 => hUone 0 2 (by decide) hU0 hU2⟩ h2
  rcases hcases with ⟨hL0, hU0⟩ | ⟨hL2, hU2⟩
  · -- both layers are attached to G_T
    by_cases hw : ¬ T.L.wm T.U ∧ ¬ T.L.wc T.U
    · -- no edge between the layers: color both B
      obtain ⟨c, hc⟩ := T.uniform_allFalse h0 hL hU 2 2 (fun h => absurd h (by decide))
        (fun h => absurd h (by decide)) (fun h => hLone 0 2 (by decide) hL0 h)
        (fun h => hUone 0 2 (by decide) hU0 h) (fun _ => hw)
      exact hv.not_allFalse hc
    by_cases hLl : ¬ T.L.matched ∧ ¬ T.L.crossed
    · -- L has no literal neighbor: color L with F and U with B
      obtain ⟨c, hc⟩ := T.uniform_allFalse h0 hL hU 1 2 (fun _ => hLl)
        (fun h => absurd h (by decide)) (fun h => hLone 0 1 (by decide) hL0 h)
        (fun h => hUone 0 2 (by decide) hU0 h) (fun h => absurd h (by decide))
      exact hv.not_allFalse hc
    by_cases hUl : ¬ T.U.matched ∧ ¬ T.U.crossed
    · -- U has no literal neighbor: color U with F and L with B
      obtain ⟨c, hc⟩ := T.uniform_allFalse h0 hL hU 2 1 (fun h => absurd h (by decide))
        (fun _ => hUl) (fun h => hLone 0 2 (by decide) hL0 h)
        (fun h => hUone 0 1 (by decide) hU0 h) (fun h => absurd h (by decide))
      exact hv.not_allFalse hc
    -- both layers are attached to the literals and to each other
    have hLl' : T.L.matched ∨ T.L.crossed := by
      by_contra h
      exact hLl ⟨fun a => h (Or.inl a), fun a => h (Or.inr a)⟩
    have hUl' : T.U.matched ∨ T.U.crossed := by
      by_contra h
      exact hUl ⟨fun a => h (Or.inl a), fun a => h (Or.inr a)⟩
    have hw' : T.L.wm T.U ∨ T.L.wc T.U := by
      by_contra h
      exact hw ⟨fun a => h (Or.inl a), fun a => h (Or.inr a)⟩
    obtain ⟨c, hc⟩ := hv.onlyTrue 2
    obtain ⟨hL0B, -⟩ := T.L.forced_B hc hL0 hLl'
    obtain ⟨hU0B, hU1B⟩ := T.U.forced_B hc hU0 hUl'
    rcases hw' with hm | hcr
    · exact hc.proper ((T.L.adj_layer T.U 0 0).mpr (by rwa [if_pos rfl])) (hL0B.trans hU0B.symm)
    · exact hc.proper ((T.L.adj_layer T.U 0 1).mpr (by rwa [if_neg (by decide)]))
        (hL0B.trans hU1B.symm)
  · -- both layers are attached to G_B: no vertex is attached to G_T or G_F
    obtain ⟨w, hw, hadj⟩ := g.cor9_i hv
    rcases g.vertex_cases w with ⟨i, rfl⟩ | ⟨t, rfl⟩ | hwaux
    · rcases hadj with h | h
      · exact (h0 i).1 h.symm
      · exact (h0 i).2 h.symm
    · exact hw t rfl
    · rcases T.all w hwaux with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rcases hadj with h | h
        · exact hLone 0 2 (by decide) ((T.L.adj_anchor i 0).mp h.symm) hL2
        · exact hLone 1 2 (by decide) ((T.L.adj_anchor i 1).mp h.symm) hL2
      · rcases hadj with h | h
        · exact hUone 0 2 (by decide) ((T.U.adj_anchor i 0).mp h.symm) hU2
        · exact hUone 1 2 (by decide) ((T.U.adj_anchor i 1).mp h.symm) hU2

/-- Lemma 14. No minimum valid gadget has two size-3 auxiliary orbits `L` and
    `U` that are both isolated layers. In a minimum gadget two size-3 orbits
    are all the auxiliary vertices, so they are exactly the two orbits of
    the paper's statement. -/
theorem lemma14 [Finite V] (hv : g.Valid) (hmin : g.IsMinimum) (L U : g.Layer)
    (hdisj : ∀ i j, L.pt i ≠ U.pt j) (hL : ¬ L.triangle) (hU : ¬ U.triangle) : False :=
  TwoLayers.not_both_isolated ⟨L, U, hdisj, (two_layers_exhaust_budget hmin L U hdisj).2⟩
    hv hmin hL hU

end Gadget

end Def1
