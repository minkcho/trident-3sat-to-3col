import proof.Basics

/-!
  # Lemma 8 (color-swap symmetry)

  If neither G_T nor G_F is adjacent to a non-anchor vertex, then (T, T, T)
  extends to a proper coloring exactly when (F, F, F) does: swap the colors
  T and F on all non-anchor vertices.
-/

namespace Def1

variable {V : Type}

/-- The color swap T ↔ F fixes B. -/
theorem swapTF_eq_two : ∀ x : Fin 3, Equiv.swap (0 : Fin 3) 1 x = 2 ↔ x = 2 := by decide

namespace Gadget

variable (g : Gadget V)

open Classical in
/-- Swap the colors T and F on the non-anchor vertices. -/
noncomputable def swapColors (c : V → Fin 3) : V → Fin 3 :=
  fun v => if ∃ t, v = g.anchor t then c v else Equiv.swap (0 : Fin 3) 1 (c v)

theorem swapColors_anchor (c : V → Fin 3) (t : Fin 3) :
    g.swapColors c (g.anchor t) = c (g.anchor t) := by
  unfold swapColors
  rw [if_pos ⟨t, rfl⟩]

theorem swapColors_of_ne (c : V → Fin 3) {v : V} (h : ∀ t, v ≠ g.anchor t) :
    g.swapColors c v = Equiv.swap (0 : Fin 3) 1 (c v) := by
  unfold swapColors
  rw [if_neg (fun ⟨t, ht⟩ => h t ht)]

/-- The swapped coloring is a coloring for the complemented input, when
    neither G_T nor G_F is adjacent to a non-anchor vertex. -/
theorem swapColors_isColoring
    (hno : ∀ v, (∀ t, v ≠ g.anchor t) → ¬ g.G.Adj g.gT v ∧ ¬ g.G.Adj g.gF v)
    {α : Fin 3 → Bool} {c : V → Fin 3} (hc : g.IsColoring α c) :
    g.IsColoring (fun i => !α i) (g.swapColors c) := by
  refine IsColoring.mk' ?_ (fun t => ?_) (fun i => ?_)
  · intro u v huv
    by_cases hu : ∃ t, u = g.anchor t
    · obtain ⟨t, rfl⟩ := hu
      rw [g.swapColors_anchor]
      by_cases hv : ∃ s, v = g.anchor s
      · obtain ⟨s, rfl⟩ := hv
        rw [g.swapColors_anchor]
        exact hc.proper huv
      · have hv' : ∀ s, v ≠ g.anchor s := fun s hs => hv ⟨s, hs⟩
        rw [g.swapColors_of_ne c hv', hc.anchor]
        have ht : t = 2 := by
          fin_cases t
          · exact absurd huv (hno v hv').1
          · exact absurd huv (hno v hv').2
          · rfl
        subst ht
        have h2 : c v ≠ 2 := fun h => hc.proper huv ((hc.anchor 2).trans h.symm)
        exact fun h => h2 ((swapTF_eq_two _).mp h.symm)
    · have hu' : ∀ t, u ≠ g.anchor t := fun t ht => hu ⟨t, ht⟩
      rw [g.swapColors_of_ne c hu']
      by_cases hv : ∃ s, v = g.anchor s
      · obtain ⟨s, rfl⟩ := hv
        rw [g.swapColors_anchor, hc.anchor]
        have hs : s = 2 := by
          fin_cases s
          · exact absurd huv.symm (hno u hu').1
          · exact absurd huv.symm (hno u hu').2
          · rfl
        subst hs
        have h2 : c u ≠ 2 := fun h => hc.proper huv (h.trans (hc.anchor 2).symm)
        exact fun h => h2 ((swapTF_eq_two _).mp h)
      · have hv' : ∀ s, v ≠ g.anchor s := fun s hs => hv ⟨s, hs⟩
        rw [g.swapColors_of_ne c hv']
        exact fun h => hc.proper huv ((Equiv.swap (0 : Fin 3) 1).injective h)
  · rw [g.swapColors_anchor]
    exact hc.anchor t
  · rw [g.swapColors_of_ne c (fun t => g.lit_ne_anchor' i t), hc.2.2.2.2 i]
    cases α i <;> decide

/-- Lemma 8 (color-swap symmetry). If neither G_T nor G_F is adjacent to a
    non-anchor vertex, then (T, T, T) extends to a proper coloring if and
    only if (F, F, F) does. -/
theorem lemma8
    (hno : ∀ v, (∀ t, v ≠ g.anchor t) → ¬ g.G.Adj g.gT v ∧ ¬ g.G.Adj g.gF v) :
    g.Extends allTrue ↔ g.Extends allFalse := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨g.swapColors c, g.swapColors_isColoring hno hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨g.swapColors c, g.swapColors_isColoring hno hc⟩

end Gadget

end Def1
