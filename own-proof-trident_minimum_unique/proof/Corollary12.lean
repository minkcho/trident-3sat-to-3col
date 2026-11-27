import proof.Lemma6

/-!
  # Corollary 12

  If a triangle module is directly connected to the literals, the gadget has
  no proper 3-coloring under the satisfying input (T, T, T): the three
  vertices of the triangle avoid T and cannot be colored with two colors.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable {g : Gadget V}

/-- A layer with a nonempty literal attachment: each vertex has a literal
    neighbor. -/
theorem Layer.exists_adj_lit (L : g.Layer) (hatt : L.matched ∨ L.crossed) (i : Fin 3) :
    ∃ j, g.G.Adj (L.pt i) (g.lit j) := by
  rcases hatt with h | h
  · exact ⟨i, (L.adj_lit i i).mpr (by rwa [if_pos rfl])⟩
  · obtain ⟨j, hji, -⟩ := exists_third i i
    exact ⟨j, (L.adj_lit i j).mpr (by rwa [if_neg (Ne.symm hji)])⟩

/-- Corollary 12. A triangle layer that is connected to the literals makes
    the gadget reject (T, T, T). -/
theorem cor12 (L : g.Layer) (htri : L.triangle) (hatt : L.matched ∨ L.crossed) :
    ¬ g.Extends allTrue := by
  intro h
  obtain ⟨c, hc⟩ := (g.extends_iff _).mp h
  have h0 : ∀ i, c (L.pt i) ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := L.exists_adj_lit hatt i
    have h1 := hc.proper hj
    rwa [hc.lit_true (i := j) rfl] at h1
  have hd : ∀ i j, i ≠ j → c (L.pt i) ≠ c (L.pt j) :=
    fun i j hij => hc.proper ((L.adj_self i j).mpr ⟨hij, htri⟩)
  exact no_triangle_two_colors 0 _ _ _ (h0 0) (h0 1) (h0 2) (hd 0 1 (by decide))
    (hd 0 2 (by decide)) (hd 1 2 (by decide))

end Gadget

end Def1
