import proof.Basics

/-!
  Removing auxiliary vertices from a gadget.

  Let `S` be a set of auxiliary vertices that the action maps to itself.
  `Removal.gadget` is the gadget on the remaining vertices, with the induced
  edges and, in addition, the edges from the anchor `t` to the vertices
  marked by `ex`. Two uses:

  * merging an orbit into an anchor (Corollary 9(ii)): `ex` marks the
    neighbors of the orbit;
  * deleting a component (the case `d = 0` of the triangle analysis): `ex`
    marks nothing.

  `restrict` and `extend` carry colorings between the two gadgets.
-/

namespace Def1

variable {V : Type}

namespace Gadget

/-- A set `S` of auxiliary vertices to remove, an anchor `t`, and a set `ex`
    of vertices to join to that anchor. Both sets are invariant under the
    action, and the anchor itself is not marked. -/
structure Removal (g : Gadget V) where
  S : V → Prop
  t : Fin 3
  ex : V → Prop
  S_aux : ∀ v, S v → g.IsAux v
  S_inv : ∀ (σ : Equiv.Perm (Fin 3)) (v : V), S v → S (g.ρ σ v)
  ex_inv : ∀ (σ : Equiv.Perm (Fin 3)) (v : V), ex (g.ρ σ v) ↔ ex v
  ex_anchor : ¬ ex (g.anchor t)

variable {g : Gadget V}

namespace Removal

variable (R : g.Removal)

theorem not_S_map (σ : Equiv.Perm (Fin 3)) {v : V} (h : ¬ R.S v) : ¬ R.S (g.ρ σ v) := by
  intro h'
  have h1 := R.S_inv σ⁻¹ _ h'
  rw [g.ρ_inv_ρ] at h1
  exact h h1

/-- The graph on the remaining vertices. -/
def graph : SimpleGraph {v : V // ¬ R.S v} :=
  SimpleGraph.fromRel fun u w => g.G.Adj u.1 w.1 ∨ (u.1 = g.anchor R.t ∧ R.ex w.1)

theorem adj_iff {u w : {v : V // ¬ R.S v}} :
    R.graph.Adj u w ↔ g.G.Adj u.1 w.1 ∨ (u.1 = g.anchor R.t ∧ R.ex w.1) ∨
      (w.1 = g.anchor R.t ∧ R.ex u.1) := by
  unfold graph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, (h | h) | (h | h)⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
  · intro h
    have hne : u ≠ w := by
      rintro rfl
      rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact g.G.irrefl h
      · exact R.ex_anchor (h1 ▸ h2)
      · exact R.ex_anchor (h1 ▸ h2)
    rcases h with h | h | h
    · exact ⟨hne, Or.inl (Or.inl h)⟩
    · exact ⟨hne, Or.inl (Or.inr h)⟩
    · exact ⟨hne, Or.inr (Or.inr h)⟩

/-- The action on the remaining vertices. -/
def perm (σ : Equiv.Perm (Fin 3)) : {v : V // ¬ R.S v} ≃ {v : V // ¬ R.S v} where
  toFun v := ⟨g.ρ σ v.1, R.not_S_map σ v.2⟩
  invFun v := ⟨g.ρ σ⁻¹ v.1, R.not_S_map σ⁻¹ v.2⟩
  left_inv v := Subtype.ext (g.ρ_inv_ρ σ v.1)
  right_inv v := Subtype.ext (g.ρ_ρ_inv σ v.1)

/-- The action is by automorphisms of the new graph. -/
def iso (σ : Equiv.Perm (Fin 3)) : R.graph ≃g R.graph where
  toEquiv := R.perm σ
  map_rel_iff' := by
    intro u w
    rw [R.adj_iff, R.adj_iff]
    show g.G.Adj (g.ρ σ u.1) (g.ρ σ w.1) ∨
      (g.ρ σ u.1 = g.anchor R.t ∧ R.ex (g.ρ σ w.1)) ∨
      (g.ρ σ w.1 = g.anchor R.t ∧ R.ex (g.ρ σ u.1)) ↔ _
    rw [g.adj_ρ, R.ex_inv, R.ex_inv, g.ρ_eq_anchor, g.ρ_eq_anchor]

/-- The gadget on the remaining vertices. -/
def gadget : Gadget {v : V // ¬ R.S v} where
  G := R.graph
  lit i := ⟨g.lit i, fun h => (R.S_aux _ h).ne_lit i rfl⟩
  gT := ⟨g.gT, fun h => (R.S_aux _ h).ne_anchor 0 rfl⟩
  gF := ⟨g.gF, fun h => (R.S_aux _ h).ne_anchor 1 rfl⟩
  gB := ⟨g.gB, fun h => (R.S_aux _ h).ne_anchor 2 rfl⟩
  lit_inj := fun _ _ h => g.lit_inj (congrArg Subtype.val h)
  lit_ne_anchor := fun i =>
    ⟨fun h => (g.lit_ne_anchor i).1 (congrArg Subtype.val h),
     fun h => (g.lit_ne_anchor i).2.1 (congrArg Subtype.val h),
     fun h => (g.lit_ne_anchor i).2.2 (congrArg Subtype.val h)⟩
  lit_nonadj := fun i j h => by
    rcases R.adj_iff.mp h with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact g.lit_nonadj i j h1
    · exact g.lit_ne_anchor' i R.t h1
    · exact g.lit_ne_anchor' j R.t h1
  palette := ⟨R.adj_iff.mpr (Or.inl g.palette.1), R.adj_iff.mpr (Or.inl g.palette.2.1),
    R.adj_iff.mpr (Or.inl g.palette.2.2)⟩
  fan := fun i => R.adj_iff.mpr (Or.inl (g.fan i))
  ρ :=
    { toFun := R.iso
      map_one' := RelIso.ext fun v => Subtype.ext (g.ρ_one v.1)
      map_mul' := fun σ τ => RelIso.ext fun v => Subtype.ext (g.ρ_mul σ τ v.1) }
  ρ_lit := fun σ i => Subtype.ext (g.ρ_lit σ i)
  ρ_anchor := fun σ => ⟨Subtype.ext (g.ρ_anchor σ).1, Subtype.ext (g.ρ_anchor σ).2.1,
    Subtype.ext (g.ρ_anchor σ).2.2⟩

theorem gadget_anchor (s : Fin 3) : (R.gadget.anchor s).1 = g.anchor s := by
  fin_cases s <;> rfl

theorem gadget_isAux {w : {v : V // ¬ R.S v}} : R.gadget.IsAux w ↔ g.IsAux w.1 := by
  constructor
  · rintro ⟨h1, hT, hF, hB⟩
    exact ⟨fun i hi => h1 i (Subtype.ext hi), fun h => hT (Subtype.ext h),
      fun h => hF (Subtype.ext h), fun h => hB (Subtype.ext h)⟩
  · rintro ⟨h1, hT, hF, hB⟩
    exact ⟨fun i hi => h1 i (congrArg Subtype.val hi), fun h => hT (congrArg Subtype.val h),
      fun h => hF (congrArg Subtype.val h), fun h => hB (congrArg Subtype.val h)⟩

/-- Removing a nonempty set leaves fewer auxiliary vertices. -/
theorem card_aux_lt [Finite V] {s : V} (hs : R.S s) :
    Nat.card {w // R.gadget.IsAux w} < Nat.card {v // g.IsAux v} := by
  have : Fintype {w // R.gadget.IsAux w} := Fintype.ofFinite _
  have : Fintype {v // g.IsAux v} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_injective_of_notMem
    (fun w : {w // R.gadget.IsAux w} => (⟨w.1.1, R.gadget_isAux.mp w.2⟩ : {v // g.IsAux v}))
    (fun a b h => by
      have h1 : a.1.1 = b.1.1 := congrArg (fun x : {v // g.IsAux v} => x.1) h
      exact Subtype.ext (Subtype.ext h1))
    (b := ⟨s, R.S_aux s hs⟩) ?_
  rintro ⟨w, hw⟩
  have h1 : w.1.1 = s := congrArg Subtype.val hw
  exact w.1.2 (h1 ▸ hs)

/-- A coloring of the gadget restricts to the remaining vertices, when the
    marked vertices avoid the color of the anchor. -/
theorem restrict {α : Fin 3 → Bool} {c : V → Fin 3} (hc : g.IsColoring α c)
    (hex : ∀ w, R.ex w → c w ≠ R.t) : R.gadget.IsColoring α (fun w => c w.1) := by
  refine ⟨?_, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
  intro u w huw
  show c u.1 ≠ c w.1
  rcases R.adj_iff.mp huw with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hc.proper h
  · rw [h1, hc.anchor]
    exact Ne.symm (hex _ h2)
  · rw [h1, hc.anchor]
    exact hex _ h2

open Classical in
/-- Extend a coloring of the remaining vertices by the colors `e` on the
    removed ones. -/
noncomputable def extendCol (c' : {v : V // ¬ R.S v} → Fin 3) (e : V → Fin 3) : V → Fin 3 :=
  fun v => if h : R.S v then e v else c' ⟨v, h⟩

theorem extendCol_S (c' : {v : V // ¬ R.S v} → Fin 3) (e : V → Fin 3) {v : V} (h : R.S v) :
    R.extendCol c' e v = e v := by
  unfold extendCol
  rw [dif_pos h]

theorem extendCol_not_S (c' : {v : V // ¬ R.S v} → Fin 3) (e : V → Fin 3)
    (w : {v : V // ¬ R.S v}) : R.extendCol c' e w.1 = c' w := by
  unfold extendCol
  rw [dif_neg w.2]

/-- A coloring of the remaining vertices extends to the gadget, when the
    colors `e` are proper on the removed vertices and against their
    neighbors. -/
theorem extend {α : Fin 3 → Bool} {c' : {v : V // ¬ R.S v} → Fin 3}
    (hc' : R.gadget.IsColoring α c') (e : V → Fin 3)
    (hSS : ∀ u w, R.S u → R.S w → g.G.Adj u w → e u ≠ e w)
    (hSO : ∀ u (w : {v : V // ¬ R.S v}), R.S u → g.G.Adj u w.1 → e u ≠ c' w) :
    g.IsColoring α (R.extendCol c' e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u w huw
    by_cases hu : R.S u
    · by_cases hw : R.S w
      · rw [R.extendCol_S c' e hu, R.extendCol_S c' e hw]
        exact hSS u w hu hw huw
      · rw [R.extendCol_S c' e hu, R.extendCol_not_S c' e ⟨w, hw⟩]
        exact hSO u ⟨w, hw⟩ hu huw
    · by_cases hw : R.S w
      · rw [R.extendCol_not_S c' e ⟨u, hu⟩, R.extendCol_S c' e hw]
        exact Ne.symm (hSO w ⟨u, hu⟩ hw huw.symm)
      · rw [R.extendCol_not_S c' e ⟨u, hu⟩, R.extendCol_not_S c' e ⟨w, hw⟩]
        exact hc'.proper (R.adj_iff.mpr (Or.inl huw))
  · exact (R.extendCol_not_S c' e R.gadget.gT).trans hc'.2.1
  · exact (R.extendCol_not_S c' e R.gadget.gF).trans hc'.2.2.1
  · exact (R.extendCol_not_S c' e R.gadget.gB).trans hc'.2.2.2.1
  · intro i
    exact (R.extendCol_not_S c' e (R.gadget.lit i)).trans (hc'.2.2.2.2 i)

end Removal

end Gadget

end Def1
