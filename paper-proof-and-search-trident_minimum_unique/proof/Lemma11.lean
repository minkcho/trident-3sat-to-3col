import proof.Lemma10

/-!
  # Lemma 11 (the degree-one channel)

  A valid clause gadget has an auxiliary vertex that is adjacent to exactly
  one literal. Otherwise the palette of every auxiliary vertex under
  (F, F, T) is contained in its palette under (F, F, F), and the gadget
  fails by mimicry (Lemma 10 with Claim 2).

  The proof in the paper ends with the remark that the argument holds for
  arbitrary clause gadgets. `ClauseGadget.lean` proves the lemma without
  the action.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable (g : Gadget V)

/-- Lemma 11, second sentence. If no auxiliary vertex is adjacent to exactly
    one literal, then `g(F, F, T) ⊆ g(F, F, F)`: the palette of every
    auxiliary vertex under (F, F, T) is contained in its palette under
    (F, F, F). -/
theorem lemma11_containment (h0 : g.NoLitAnchor)
    (hno : ¬ ∃ v, g.IsAux v ∧ ∃ k : Fin 3, ∀ j, g.G.Adj v (g.lit j) ↔ j = k) :
    ∀ a, g.AuxColoring (onlyTrue 2) a → g.AuxColoring allFalse a := by
  refine g.palette_claim h0 ?_
  intro v hvaux d hd i hi
  -- `d` avoids the colors of the literal neighbors under (F, F, T); show `d ≠ F`
  show d ≠ if allFalse i then 0 else 1
  by_cases hi2 : i = 2
  · -- `v` sees `lit 2`; it is not its only literal neighbor, so it sees a false literal
    have hex : ∃ j, j ≠ 2 ∧ g.G.Adj v (g.lit j) := by
      by_contra hnone
      refine hno ⟨v, hvaux, 2, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
      · by_contra hj2
        exact hnone ⟨j, hj2, hj⟩
      · rw [hj, ← hi2]
        exact hi
    obtain ⟨j, hj2, hj⟩ := hex
    have h1 := hd j hj
    have h2 : onlyTrue 2 j = false := by simp [onlyTrue, hj2]
    rw [h2] at h1
    exact h1
  · have h1 := hd i hi
    have h2 : onlyTrue 2 i = false := by simp [onlyTrue, hi2]
    rw [h2] at h1
    exact h1

/-- Lemma 11 (the degree-one channel). A valid gadget has an auxiliary
    vertex that is adjacent to exactly one literal: otherwise it fails by
    mimicry. -/
theorem lemma11 (hv : g.Valid) :
    ∃ v, g.IsAux v ∧ ∃ k : Fin 3, ∀ j, g.G.Adj v (g.lit j) ↔ j = k := by
  by_contra hno
  exact g.lemma10 (α := onlyTrue 2) ⟨2, by simp [onlyTrue]⟩
    (g.lemma11_containment hv.noLitAnchor hno) hv

end Gadget

end Def1
