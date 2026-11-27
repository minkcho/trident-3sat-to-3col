import proof.Basics

/-!
  # Lemma 10 (mimicry) and Claim 2 (palettes)

  For an input `α`, `g(α)` is the set of colorings of the auxiliary vertices
  that are proper when the literals are colored by `α` and the anchors are
  fixed. Here `g.AuxColoring α a` says that `a` belongs to `g(α)`: `a` is
  the auxiliary part of a proper coloring for `α`.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable (g : Gadget V)

/-- `a ∈ g(α)`: the coloring `a` of the auxiliary vertices is proper
    together with the literals colored by `α` and the fixed anchors. -/
def AuxColoring (α : Fin 3 → Bool) (a : V → Fin 3) : Prop :=
  ∃ c, g.IsColoring α c ∧ ∀ v, g.IsAux v → c v = a v

/-- Lemma 10 (mimicry). If `g(α) ⊆ g(F, F, F)` for a satisfying input `α`,
    the gadget is not valid: an accepted `α` gives an auxiliary coloring
    that also works for (F, F, F). -/
theorem lemma10 {α : Fin 3 → Bool} (hα : ∃ i, α i = true)
    (h : ∀ a, g.AuxColoring α a → g.AuxColoring allFalse a) : ¬ g.Valid := by
  intro hv
  obtain ⟨i, hi⟩ := hα
  obtain ⟨c, hc⟩ := hv.of_true hi
  obtain ⟨c', hc', -⟩ := h c ⟨c, hc, fun _ _ => rfl⟩
  exact hv.not_allFalse hc'

/-- The palette of a vertex under an input: the colors not used by its
    literal neighbors. -/
def vertexPalette (α : Fin 3 → Bool) (v : V) : Set (Fin 3) :=
  {d | ∀ i, g.G.Adj v (g.lit i) → d ≠ if α i then 0 else 1}

/-- Claim 2. If the palette of every auxiliary vertex under `α`
    is contained in its palette under (F, F, F), then
    `g(α) ⊆ g(F, F, F)`. The standing assumption is used for the edges
    between literals and anchors. -/
theorem palette_claim (h0 : g.NoLitAnchor) {α : Fin 3 → Bool}
    (hp : ∀ v, g.IsAux v → g.vertexPalette α v ⊆ g.vertexPalette allFalse v) :
    ∀ a, g.AuxColoring α a → g.AuxColoring allFalse a := by
  rintro a ⟨c, hc, hca⟩
  have hlit : ∀ i, recolor c g.lit (fun _ => (1 : Fin 3)) (g.lit i) = 1 :=
    fun i => recolor_apply c g.lit_inj _ i
  have hne : ∀ v, (∀ i, v ≠ g.lit i) → recolor c g.lit (fun _ => (1 : Fin 3)) v = c v :=
    fun v hv => recolor_of_ne c _ (fun i hi => hv i hi.symm)
  refine ⟨recolor c g.lit (fun _ => 1), IsColoring.mk' ?_ (fun t => ?_) (fun i => ?_), ?_⟩
  · refine proper_of_agree (fun v => ∃ i, v = g.lit i) hc.1
      (fun v hv => hne v (fun i hi => hv ⟨i, hi⟩)) ?_
    rintro u v ⟨i, rfl⟩ huv
    rw [hlit i]
    rcases g.vertex_cases v with ⟨j, rfl⟩ | ⟨t, rfl⟩ | hv
    · exact absurd huv (g.lit_nonadj i j)
    · rw [hne _ (fun j hj => g.lit_ne_anchor' j t hj.symm), hc.anchor, h0.eq_two huv]
      decide
    · rw [hne v hv.ne_lit]
      have hmem : c v ∈ g.vertexPalette α v := by
        intro j hj
        have h1 := hc.proper hj
        rwa [hc.2.2.2.2 j] at h1
      have h2 := hp v hv hmem i huv.symm
      exact fun h => h2 h.symm
  · rw [hne _ (fun j hj => g.lit_ne_anchor' j t hj.symm)]
    exact hc.anchor t
  · rw [hlit i]
    rfl
  · intro v hv
    rw [hne v hv.ne_lit]
    exact hca v hv

end Gadget

end Def1
