import proof.Lemma8
import proof.Lemma6
import proof.Removal
import proof.TridentGadget

/-!
  # Corollary 9 (anchor normalization)

  (i) In a valid gadget, G_T or G_F is adjacent to a non-anchor vertex
  (Lemma 8).

  (ii) In a minimum valid gadget, every auxiliary vertex is adjacent to at
  most one palette anchor. As in the paper: a vertex adjacent to two anchors
  has the third color in every coloring, and so has its whole orbit. No edge
  joins two vertices of the orbit, and none joins the orbit to the anchor of
  that color. Merging the orbit into this anchor gives a smaller gadget that
  accepts the same inputs, against minimality.
-/

namespace Def1

variable {V : Type}

/-- A color different from two different colors is the third color. -/
theorem forced_color : ∀ x s t r : Fin 3,
    s ≠ t → r ≠ s → r ≠ t → x ≠ s → x ≠ t → x = r := by decide

namespace Gadget

variable (g : Gadget V)

/-- Corollary 9(i). In a valid gadget at least one of G_T and G_F is
    adjacent to a non-anchor vertex. -/
theorem cor9_i (hv : g.Valid) :
    ∃ v, (∀ t, v ≠ g.anchor t) ∧ (g.G.Adj g.gT v ∨ g.G.Adj g.gF v) := by
  by_contra hno
  have hno' : ∀ v, (∀ t, v ≠ g.anchor t) → ¬ g.G.Adj g.gT v ∧ ¬ g.G.Adj g.gF v :=
    fun v hv' => ⟨fun h => hno ⟨v, hv', Or.inl h⟩, fun h => hno ⟨v, hv', Or.inr h⟩⟩
  obtain ⟨c, hc⟩ := hv.allTrue
  obtain ⟨c', hc'⟩ := (g.extends_iff _).mp ((g.lemma8 hno').mp ⟨c, hc⟩)
  exact hv.not_allFalse hc'

/-- `g` has at most as many auxiliary vertices as every valid gadget on a
    finite vertex set. A valid gadget with this property is a minimum valid
    gadget. -/
def IsMinimum : Prop :=
  ∀ (V' : Type) [Finite V'] (g' : Gadget V'), g'.Valid →
    Nat.card {v // g.IsAux v} ≤ Nat.card {v // g'.IsAux v}

/-- A minimum gadget has at most six auxiliary vertices, since the trident
    is valid with six (Theorem 4). -/
theorem IsMinimum.card_le_six {g : Gadget V} (hmin : g.IsMinimum) :
    Nat.card {v // g.IsAux v} ≤ 6 := by
  have h1 := hmin TV tridentGadget tridentGadget_valid
  rwa [tridentGadget_card_aux] at h1

/-- Corollary 9(ii). In a minimum valid gadget no auxiliary vertex is
    adjacent to two palette anchors. -/
theorem cor9_ii [Finite V] (hv : g.Valid) (hmin : g.IsMinimum) {v : V} (hvaux : g.IsAux v)
    {s t : Fin 3} (hst : s ≠ t) (hs : g.G.Adj v (g.anchor s)) (ht : g.G.Adj v (g.anchor t)) :
    False := by
  obtain ⟨r, hrs, hrt⟩ := exists_third s t
  -- every vertex of the orbit of v is adjacent to the same two anchors
  have hSadj : ∀ w, (∃ σ, g.ρ σ v = w) →
      g.G.Adj w (g.anchor s) ∧ g.G.Adj w (g.anchor t) := by
    rintro w ⟨σ, rfl⟩
    constructor
    · have h1 := (g.adj_ρ σ).mpr hs
      rwa [g.ρ_anchor'] at h1
    · have h1 := (g.adj_ρ σ).mpr ht
      rwa [g.ρ_anchor'] at h1
  -- so it has the third color r in every coloring
  have hforced : ∀ {α : Fin 3 → Bool} {c : V → Fin 3}, g.IsColoring α c →
      ∀ w, (∃ σ, g.ρ σ v = w) → c w = r := by
    intro α c hc w hw
    obtain ⟨h1, h2⟩ := hSadj w hw
    refine forced_color _ s t r hst hrs hrt ?_ ?_
    · have h3 := hc.proper h1
      rwa [hc.anchor] at h3
    · have h3 := hc.proper h2
      rwa [hc.anchor] at h3
  obtain ⟨c0, hc0⟩ := hv.allTrue
  have hnoSS : ∀ u w, (∃ σ, g.ρ σ v = u) → (∃ σ, g.ρ σ v = w) → ¬ g.G.Adj u w :=
    fun u w hu hw h => hc0.proper h ((hforced hc0 u hu).trans (hforced hc0 w hw).symm)
  have hnoSr : ∀ u, (∃ σ, g.ρ σ v = u) → ¬ g.G.Adj u (g.anchor r) :=
    fun u hu h => hc0.proper h ((hforced hc0 u hu).trans (hc0.anchor r).symm)
  -- merge the orbit into the anchor of color r
  let R : g.Removal :=
    { S := fun w => ∃ σ, g.ρ σ v = w
      t := r
      ex := fun w => ∃ o, (∃ σ, g.ρ σ v = o) ∧ g.G.Adj o w
      S_aux := by
        rintro w ⟨σ, rfl⟩
        exact g.isAux_map σ hvaux
      S_inv := by
        rintro τ w ⟨σ, rfl⟩
        exact ⟨τ * σ, g.ρ_mul τ σ v⟩
      ex_inv := by
        intro τ w
        constructor
        · rintro ⟨o, ⟨σ, rfl⟩, ho⟩
          refine ⟨g.ρ (τ⁻¹ * σ) v, ⟨_, rfl⟩, ?_⟩
          rw [g.ρ_mul]
          have h1 := (g.adj_ρ τ⁻¹).mpr ho
          rwa [g.ρ_inv_ρ] at h1
        · rintro ⟨o, ⟨σ, rfl⟩, ho⟩
          refine ⟨g.ρ (τ * σ) v, ⟨_, rfl⟩, ?_⟩
          rw [g.ρ_mul]
          exact (g.adj_ρ τ).mpr ho
      ex_anchor := by
        rintro ⟨o, ho, h⟩
        exact hnoSr o ho h }
  -- the merged gadget accepts the same inputs
  have hvalid : R.gadget.Valid := by
    intro α
    rw [← hv α]
    constructor
    · intro h
      obtain ⟨c', hc'⟩ := (R.gadget.extends_iff α).mp h
      refine ⟨R.extendCol c' (fun _ => r), R.extend hc' _ ?_ ?_⟩
      · intro u w hu hw h1
        exact absurd h1 (hnoSS u w hu hw)
      · intro u w hu h1
        have hadj : R.gadget.G.Adj (R.gadget.anchor r) w :=
          R.adj_iff.mpr (Or.inr (Or.inl ⟨R.gadget_anchor r, u, hu, h1⟩))
        have h2 := hc'.proper hadj
        rwa [hc'.anchor] at h2
    · intro h
      obtain ⟨c, hc⟩ := (g.extends_iff α).mp h
      refine ⟨fun w => c w.1, R.restrict hc ?_⟩
      rintro w ⟨o, ho, how⟩
      have h1 := hc.proper how
      rw [hforced hc o ho] at h1
      exact Ne.symm h1
  have hlt := R.card_aux_lt (s := v) ⟨1, g.ρ_one v⟩
  have hle := hmin _ R.gadget hvalid
  omega

end Gadget

end Def1
