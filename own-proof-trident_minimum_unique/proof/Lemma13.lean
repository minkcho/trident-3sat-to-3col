import proof.Lemma6

/-!
  # Lemma 13 (matched base extensions)

  The matched base is an isolated size-3 orbit `P = {p_0, p_1, p_2}` matched
  to the literals: `p_i` is adjacent to `x_i` and to no other literal, and
  `P` has no internal edge. A gadget built on the matched base and extended
  by any number of singleton orbits is not valid, whatever the edges among
  the singletons and the anchor attachments are.

  Proof, as in the paper. Take a proper coloring for the mixed input
  (F, F, T). A singleton adjacent to a literal is adjacent to all three and
  has color B. All vertices of `P` have the same neighbors outside `P` and
  the literals; let `D` be the set of colors not used by these common
  neighbors. If B ∈ D, recolor `P` with B; otherwise T ∈ D, and recolor `P`
  with T. Then recolor all literals with F: the result is a proper coloring
  for (F, F, F).

  The argument uses a singleton only through the even permutations, which
  fix it. `lemma13_of_even_fixed` is the argument under this weaker
  hypothesis, which also covers orbits of size 2, and `lemma13` is the
  statement of the paper.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable (g : Gadget V)

/-- The argument of Lemma 13, for an isolated size-3 orbit `P` with a matched
    literal attachment and other auxiliary vertices that the even
    permutations fix (orbits of size 1 or 2). -/
theorem lemma13_of_even_fixed (P : g.Layer) (hm : P.matched) (hiso : ¬ P.triangle)
    (hfix : ∀ w, g.IsAux w → (∀ i, w ≠ P.pt i) →
      ∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ w = w) : ¬ g.Valid := by
  intro hv
  have h0 := hv.noLitAnchor
  obtain ⟨c, hc⟩ := hv.onlyTrue 2
  have hx0 : c (g.lit 0) = 1 := hc.lit_false (by decide)
  have hx2 : c (g.lit 2) = 0 := hc.lit_true (by decide)
  -- a singleton adjacent to a literal is adjacent to all three and has color B
  have hsB : ∀ w, g.IsAux w → (∀ i, w ≠ P.pt i) → ∀ i, g.G.Adj (g.lit i) w → c w = 2 := by
    intro w hw hwP i hi
    have hall : ∀ j, g.G.Adj w (g.lit j) := fun j =>
      (g.adj_lit_of_even_fixed (hfix w hw hwP) i j).mp hi.symm
    refine eq_two_of_ne _ ?_ ?_
    · have h1 := hc.proper (hall 2)
      rwa [hx2] at h1
    · have h1 := hc.proper (hall 0)
      rwa [hx0] at h1
  -- all vertices of P have the same neighbors outside P and the literals
  have hcommon : ∀ w, (∀ i, w ≠ g.lit i) → (∀ i, w ≠ P.pt i) →
      ∀ i j, g.G.Adj (P.pt i) w ↔ g.G.Adj (P.pt j) w := by
    intro w hwl hwP i j
    refine P.adj_fixed (fun σ hσ => ?_) i j
    rcases g.vertex_cases w with ⟨k, rfl⟩ | ⟨t, rfl⟩ | hw
    · exact absurd rfl (hwl k)
    · exact g.ρ_anchor' σ t
    · exact hfix w hw hwP σ hσ
  -- D: the colors not used by the common neighbors
  have hpD : ∀ i w, (∀ j, w ≠ g.lit j) → (∀ j, w ≠ P.pt j) → g.G.Adj (P.pt 0) w →
      c w ≠ c (P.pt i) := by
    intro i w hwl hwP hadj
    have h1 := hc.proper ((hcommon w hwl hwP 0 i).mp hadj)
    exact fun h => h1 h.symm
  have hpx : c (P.pt 0) ≠ 1 := by
    have h1 := hc.proper ((P.adj_lit 0 0).mpr (by rwa [if_pos rfl]))
    rwa [hx0] at h1
  -- the new color d of P: in D and different from F
  obtain ⟨d, hdD, hd1⟩ : ∃ d : Fin 3, (∀ w, (∀ j, w ≠ g.lit j) → (∀ j, w ≠ P.pt j) →
      g.G.Adj (P.pt 0) w → c w ≠ d) ∧ d ≠ 1 := by
    by_cases hB : ∀ w, (∀ j, w ≠ g.lit j) → (∀ j, w ≠ P.pt j) → g.G.Adj (P.pt 0) w → c w ≠ 2
    · exact ⟨2, hB, by decide⟩
    · have h2 : c (P.pt 0) ≠ 2 := fun h => hB (h ▸ hpD 0)
      have h3 : c (P.pt 0) = 0 := eq_zero_of_ne _ hpx h2
      refine ⟨0, fun w hwl hwP hadj => ?_, by decide⟩
      have h4 := hpD 0 w hwl hwP hadj
      rwa [h3] at h4
  -- recolor the literals with F and P with d
  have hP : ∀ i, recolor (recolor c g.lit fun _ => (1 : Fin 3)) P.pt (fun _ => d) (P.pt i) = d :=
    fun i => recolor_apply _ P.inj _ i
  have hL : ∀ i, recolor (recolor c g.lit fun _ => (1 : Fin 3)) P.pt (fun _ => d) (g.lit i) = 1 :=
    fun i => (recolor_of_ne _ _ (fun j => P.pt_ne_lit j i)).trans (recolor_apply c g.lit_inj _ i)
  have hO : ∀ v, (∀ i, v ≠ g.lit i) → (∀ i, v ≠ P.pt i) →
      recolor (recolor c g.lit fun _ => (1 : Fin 3)) P.pt (fun _ => d) v = c v :=
    fun v h1 h2 => (recolor_of_ne _ _ (fun i hi => h2 i hi.symm)).trans
      (recolor_of_ne c _ (fun i hi => h1 i hi.symm))
  refine hv.not_allFalse (c := recolor (recolor c g.lit fun _ => (1 : Fin 3)) P.pt (fun _ => d))
    (IsColoring.mk' ?_ (fun t => ?_) (fun i => ?_))
  · refine proper_of_agree (fun v => (∃ i, v = g.lit i) ∨ ∃ i, v = P.pt i) hc.1
      (fun v hv' => hO v (fun i hi => hv' (Or.inl ⟨i, hi⟩)) (fun i hi => hv' (Or.inr ⟨i, hi⟩))) ?_
    rintro u v (⟨i, rfl⟩ | ⟨i, rfl⟩) huv
    · -- u is the literal x_i, recolored F
      rw [hL i]
      by_cases hvl : ∃ j, v = g.lit j
      · obtain ⟨j, rfl⟩ := hvl
        exact absurd huv (g.lit_nonadj i j)
      by_cases hvP : ∃ j, v = P.pt j
      · obtain ⟨j, rfl⟩ := hvP
        rw [hP j]
        exact Ne.symm hd1
      · have hvl' : ∀ j, v ≠ g.lit j := fun j hj => hvl ⟨j, hj⟩
        have hvP' : ∀ j, v ≠ P.pt j := fun j hj => hvP ⟨j, hj⟩
        rw [hO v hvl' hvP']
        rcases g.vertex_cases v with ⟨j, rfl⟩ | ⟨t, rfl⟩ | hvaux
        · exact absurd rfl (hvl' j)
        · rw [hc.anchor, h0.eq_two huv]
          decide
        · rw [hsB v hvaux hvP' i huv]
          decide
    · -- u is the vertex p_i, recolored d
      rw [hP i]
      by_cases hvl : ∃ j, v = g.lit j
      · obtain ⟨j, rfl⟩ := hvl
        rw [hL j]
        exact hd1
      by_cases hvP : ∃ j, v = P.pt j
      · obtain ⟨j, rfl⟩ := hvP
        exact absurd ((P.adj_self i j).mp huv).2 hiso
      · have hvl' : ∀ j, v ≠ g.lit j := fun j hj => hvl ⟨j, hj⟩
        have hvP' : ∀ j, v ≠ P.pt j := fun j hj => hvP ⟨j, hj⟩
        rw [hO v hvl' hvP']
        exact Ne.symm (hdD v hvl' hvP' ((hcommon v hvl' hvP' i 0).mp huv))
  · rw [hO _ (fun j hj => g.lit_ne_anchor' j t hj.symm) (fun j hj => P.pt_ne_anchor j t hj.symm)]
    exact hc.anchor t
  · rw [hL i]
    rfl

/-- Lemma 13 (matched base extensions). A gadget built on the matched base
    `P` and extended by any number of singleton orbits is not valid. The
    hypothesis `¬ P.crossed` is part of the matched base, but the proof does
    not use it. -/
theorem lemma13 (P : g.Layer) (hm : P.matched) (_hnc : ¬ P.crossed) (hiso : ¬ P.triangle)
    (hsing : ∀ w, g.IsAux w → (∀ i, w ≠ P.pt i) → ∀ σ, g.ρ σ w = w) : ¬ g.Valid :=
  g.lemma13_of_even_fixed P hm hiso fun w hw hwP σ _ => hsing w hw hwP σ

end Gadget

end Def1
