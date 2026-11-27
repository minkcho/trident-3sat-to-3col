import proof.TwoLayers
import proof.Corollary9
import proof.Corollary12
import proof.Lemma13

/-!
  # The triangle analysis (after Lemma 14)

  The matched base `P` together with a second size-3 orbit `U` that is a
  triangle. As in the paper:

  * `U` is not attached to the literals (Corollary 12) and not to an anchor,
    which would leave the triangle two colors.
  * The wiring between `P` and `U`: with no edge (`d = 0`) the triangle adds
    no input constraint, and the matched base alone is invalid (Lemma 13);
    with complete wiring (`d = 3`) one branch vertex forbids its color on the
    whole triangle; with crossed wiring (`d = 2`) each `p_i` has the color of
    `u_i`, so the branch layer uses all three colors and cannot avoid T under
    (T, T, T). Hence the wiring is matched (`d = 1`).
  * The branch layer is attached to G_T: with no T/F anchor the color-swap
    symmetry applies (Corollary 9(i)), and with G_F the input (T, T, T)
    forces every branch to B and leaves the triangle two colors.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable {g : Gadget V}

/-- The case `d = 0`: a second layer with no edge to the rest adds no input
    constraint and cannot repair the matched base. Deleting it leaves the
    matched base, which is invalid by Lemma 13. -/
theorem no_disconnected_layer (T : g.TwoLayers) (hv : g.Valid) (hPm : T.L.matched)
    (hPc : ¬ T.L.crossed) (hPiso : ¬ T.L.triangle)
    (hUlit : ¬ T.U.matched ∧ ¬ T.U.crossed) (hUanch : ∀ t, ¬ T.U.anch t)
    (hw : ¬ T.L.wm T.U ∧ ¬ T.L.wc T.U) : False := by
  -- the layer has no edge to a vertex outside it
  have hUout : ∀ (i : Fin 3) (w : V), (∀ j, w ≠ T.U.pt j) → ¬ g.G.Adj (T.U.pt i) w := by
    intro i w hw' hadj
    rcases g.vertex_cases w with ⟨j, rfl⟩ | ⟨t, rfl⟩ | hwaux
    · have h1 := (T.U.adj_lit i j).mp hadj
      split at h1
      · exact hUlit.1 h1
      · exact hUlit.2 h1
    · exact hUanch t ((T.U.adj_anchor i t).mp hadj)
    · rcases T.all w hwaux with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have h1 := (T.L.adj_layer T.U j i).mp hadj.symm
        split at h1
        · exact hw.1 h1
        · exact hw.2 h1
      · exact hw' j rfl
  let R : g.Removal :=
    { S := fun w => ∃ i, w = T.U.pt i
      t := 0
      ex := fun _ => False
      S_aux := by
        rintro w ⟨i, rfl⟩
        exact T.U.aux i
      S_inv := by
        rintro σ w ⟨i, rfl⟩
        exact ⟨σ i, T.U.map σ i⟩
      ex_inv := fun _ _ => Iff.rfl
      ex_anchor := id }
  -- the gadget without this layer accepts the same inputs
  have hvalid : R.gadget.Valid := by
    intro α
    rw [← hv α]
    constructor
    · intro h
      obtain ⟨c', hc'⟩ := (R.gadget.extends_iff α).mp h
      refine ⟨R.extendCol c' (recolor (fun _ => 0) T.U.pt (fun i => i)), R.extend hc' _ ?_ ?_⟩
      · rintro u w ⟨i, rfl⟩ ⟨j, rfl⟩ h1
        rw [recolor_apply _ T.U.inj, recolor_apply _ T.U.inj]
        exact ((T.U.adj_self i j).mp h1).1
      · rintro u w ⟨i, rfl⟩ h1
        exact absurd h1 (hUout i w.1 (fun j hj => w.2 ⟨j, hj⟩))
    · intro h
      obtain ⟨c, hc⟩ := (g.extends_iff α).mp h
      exact ⟨fun w => c w.1, R.restrict hc (fun _ h1 => h1.elim)⟩
  -- what is left is the matched base
  let P' : R.gadget.Layer :=
    { pt := fun i => ⟨T.L.pt i, fun ⟨j, hj⟩ => T.disj i j hj⟩
      map := fun σ i => Subtype.ext (T.L.map σ i)
      inj := fun i j h => T.L.inj (congrArg Subtype.val h)
      aux := fun i => R.gadget_isAux.mpr (T.L.aux i) }
  refine R.gadget.lemma13 P' ?_ ?_ ?_ ?_ hvalid
  · exact R.adj_iff.mpr (Or.inl hPm)
  · intro h
    rcases R.adj_iff.mp h with h1 | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact hPc h1
    · exact h1
    · exact h1
  · intro h
    rcases R.adj_iff.mp h with h1 | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact hPiso h1
    · exact h1
    · exact h1
  · intro w hw' hwP σ
    exfalso
    rcases T.all w.1 (R.gadget_isAux.mp hw') with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hwP i (Subtype.ext hi)
    · exact w.2 ⟨i, hi⟩

/-- The triangle analysis. In a minimum valid gadget whose auxiliary
    vertices are the matched base `T.L` and a triangle `T.U`: the triangle
    is attached neither to the literals nor to an anchor, the wiring between
    the two layers is matched, and the branch layer is attached to G_T
    only. -/
theorem triangle_analysis [Finite V] (T : g.TwoLayers) (hv : g.Valid) (hmin : g.IsMinimum)
    (hPm : T.L.matched) (hPc : ¬ T.L.crossed) (hPiso : ¬ T.L.triangle)
    (hUtri : T.U.triangle) :
    (¬ T.U.matched ∧ ¬ T.U.crossed) ∧ (∀ t, ¬ T.U.anch t) ∧
    (T.L.wm T.U ∧ ¬ T.L.wc T.U) ∧ (T.L.anch 0 ∧ ¬ T.L.anch 1 ∧ ¬ T.L.anch 2) := by
  have h0 := hv.noLitAnchor
  obtain ⟨c, hc⟩ := hv.allTrue
  have hud : ∀ i j, i ≠ j → c (T.U.pt i) ≠ c (T.U.pt j) :=
    fun i j hij => hc.proper ((T.U.adj_self i j).mpr ⟨hij, hUtri⟩)
  have hu01 := hud 0 1 (by decide)
  have hu02 := hud 0 2 (by decide)
  have hu12 := hud 1 2 (by decide)
  -- the triangle is not attached to the literals (Corollary 12)
  have hUlit : ¬ T.U.matched ∧ ¬ T.U.crossed :=
    ⟨fun h => cor12 T.U hUtri (Or.inl h) ⟨c, hc⟩, fun h => cor12 T.U hUtri (Or.inr h) ⟨c, hc⟩⟩
  -- nor to an anchor
  have hUanch : ∀ t, ¬ T.U.anch t := by
    intro t ht
    have h1 : ∀ i, c (T.U.pt i) ≠ t := by
      intro i
      have h2 := hc.proper ((T.U.adj_anchor i t).mpr ht)
      rwa [hc.anchor] at h2
    exact no_triangle_two_colors t _ _ _ (h1 0) (h1 1) (h1 2) hu01 hu02 hu12
  -- under (T, T, T) no branch vertex has color T
  have hp0 : ∀ i, c (T.L.pt i) ≠ 0 := by
    intro i
    have h1 := hc.proper ((T.L.adj_lit i i).mpr (by rwa [if_pos rfl]))
    rwa [hc.lit_true (i := i) rfl] at h1
  -- the wiring is matched
  have hwm : T.L.wm T.U := by
    by_contra hnm
    by_cases hwc : T.L.wc T.U
    · -- d = 2: each p_i has the color of u_i
      have hk : ∀ i k, c (T.L.pt i) = c (T.U.pt k) → k = i := by
        intro i k h
        by_contra hne
        refine hc.proper ((T.L.adj_layer T.U i k).mpr ?_) h
        rw [if_neg (fun h' => hne h'.symm)]
        exact hwc
      have hpu : ∀ i, c (T.L.pt i) = c (T.U.pt i) := by
        intro i
        rcases color_mem_of_three _ _ _ (c (T.L.pt i)) hu01 hu02 hu12 with h | h | h
        · have h' := hk i 0 h
          subst h'
          exact h
        · have h' := hk i 1 h
          subst h'
          exact h
        · have h' := hk i 2 h
          subst h'
          exact h
      rcases color_mem_of_three _ _ _ (0 : Fin 3) hu01 hu02 hu12 with h | h | h
      · exact hp0 0 ((hpu 0).trans h.symm)
      · exact hp0 1 ((hpu 1).trans h.symm)
      · exact hp0 2 ((hpu 2).trans h.symm)
    · -- d = 0
      exact no_disconnected_layer T hv hPm hPc hPiso hUlit hUanch ⟨hnm, hwc⟩
  have hnwc : ¬ T.L.wc T.U := by
    intro hwc
    -- d = 3: p_0 sees the whole triangle
    have h1 : ∀ k, c (T.L.pt 0) ≠ c (T.U.pt k) := by
      intro k
      refine hc.proper ((T.L.adj_layer T.U 0 k).mpr ?_)
      split
      · exact hwm
      · exact hwc
    rcases color_mem_of_three _ _ _ (c (T.L.pt 0)) hu01 hu02 hu12 with h | h | h
    · exact h1 0 h
    · exact h1 1 h
    · exact h1 2 h
  -- the anchor of the branch layer
  have hP1 : ¬ T.L.anch 1 := by
    intro h1
    have hpB : ∀ i, c (T.L.pt i) = 2 := by
      intro i
      refine eq_two_of_ne _ (hp0 i) ?_
      have h2 := hc.proper ((T.L.adj_anchor i 1).mpr h1)
      rwa [hc.anchor] at h2
    have hu2 : ∀ i, c (T.U.pt i) ≠ 2 := by
      intro i
      have h2 := hc.proper ((T.L.adj_layer T.U i i).mpr (by rwa [if_pos rfl]))
      rw [hpB i] at h2
      exact fun h => h2 h.symm
    exact no_triangle_two_colors 2 _ _ _ (hu2 0) (hu2 1) (hu2 2) hu01 hu02 hu12
  have hP0 : T.L.anch 0 := by
    by_contra hP0
    obtain ⟨w, hw, hadj⟩ := g.cor9_i hv
    rcases g.vertex_cases w with ⟨i, rfl⟩ | ⟨t, rfl⟩ | hwaux
    · rcases hadj with h | h
      · exact (h0 i).1 h.symm
      · exact (h0 i).2 h.symm
    · exact hw t rfl
    · rcases T.all w hwaux with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rcases hadj with h | h
        · exact hP0 ((T.L.adj_anchor i 0).mp h.symm)
        · exact hP1 ((T.L.adj_anchor i 1).mp h.symm)
      · rcases hadj with h | h
        · exact hUanch 0 ((T.U.adj_anchor i 0).mp h.symm)
        · exact hUanch 1 ((T.U.adj_anchor i 1).mp h.symm)
  exact ⟨hUlit, hUanch, ⟨hwm, hnwc⟩, hP0, hP1,
    fun h2 => g.cor9_ii hv hmin (T.L.aux 0) (s := 0) (t := 2) (by decide) hP0 h2⟩

end Gadget

end Def1
