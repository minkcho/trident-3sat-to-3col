import proof.Definition1
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
  Basic facts about a gadget of Definition 1 (`Definition1.lean`): the
  anchors as a family, the action `g.ρ`, colorings and inputs, the standing
  assumption of the paper's Section IV-A (no edge joins a literal to G_T or
  G_F), and tools for recoloring and for counting auxiliary vertices.

  Colors: 0 = T, 1 = F, 2 = B.
-/

namespace Def1

variable {V : Type}

-- ------------------------------------------------------- three colors

theorem eq_two_of_ne : ∀ x : Fin 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide

theorem eq_zero_of_ne : ∀ x : Fin 3, x ≠ 1 → x ≠ 2 → x = 0 := by decide

/-- A triangle cannot be colored with two colors: three pairwise different
    colors that all avoid one color do not exist. -/
theorem no_triangle_two_colors : ∀ d x y z : Fin 3,
    x ≠ d → y ≠ d → z ≠ d → x ≠ y → x ≠ z → y ≠ z → False := by decide

/-- Three pairwise different colors are all the colors. -/
theorem color_mem_of_three : ∀ x y z d : Fin 3,
    x ≠ y → x ≠ z → y ≠ z → d = x ∨ d = y ∨ d = z := by decide

namespace Gadget

variable (g : Gadget V)

-- ------------------------------------------------------------ the anchors

/-- The anchors as a family: `anchor 0 = gT`, `anchor 1 = gF`,
    `anchor 2 = gB`. In a coloring, `anchor t` has the color `t`. -/
def anchor : Fin 3 → V
  | 0 => g.gT
  | 1 => g.gF
  | 2 => g.gB

theorem anchor_adj {s t : Fin 3} (h : s ≠ t) : g.G.Adj (g.anchor s) (g.anchor t) := by
  have hTF := g.palette.1
  have hFB := g.palette.2.1
  have hBT := g.palette.2.2
  fin_cases s <;> fin_cases t
  · exact absurd rfl h
  · exact hTF
  · exact hBT.symm
  · exact hTF.symm
  · exact absurd rfl h
  · exact hFB
  · exact hBT
  · exact hFB.symm
  · exact absurd rfl h

theorem anchor_injective : Function.Injective g.anchor := by
  intro s t h
  by_contra hst
  exact (g.anchor_adj hst).ne h

theorem lit_ne_anchor' (i t : Fin 3) : g.lit i ≠ g.anchor t := by
  fin_cases t
  · exact (g.lit_ne_anchor i).1
  · exact (g.lit_ne_anchor i).2.1
  · exact (g.lit_ne_anchor i).2.2

theorem ρ_anchor' (σ : Equiv.Perm (Fin 3)) (t : Fin 3) : g.ρ σ (g.anchor t) = g.anchor t := by
  fin_cases t
  · exact (g.ρ_anchor σ).1
  · exact (g.ρ_anchor σ).2.1
  · exact (g.ρ_anchor σ).2.2

theorem isAux_iff {v : V} : g.IsAux v ↔ (∀ i, v ≠ g.lit i) ∧ ∀ t, v ≠ g.anchor t := by
  constructor
  · rintro ⟨h1, hT, hF, hB⟩
    refine ⟨h1, fun t => ?_⟩
    fin_cases t
    · exact hT
    · exact hF
    · exact hB
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 0, h2 1, h2 2⟩

/-- Every vertex is a literal, an anchor, or an auxiliary vertex. -/
theorem vertex_cases (v : V) :
    (∃ i, v = g.lit i) ∨ (∃ t, v = g.anchor t) ∨ g.IsAux v := by
  by_cases h1 : ∃ i, v = g.lit i
  · exact Or.inl h1
  by_cases h2 : ∃ t, v = g.anchor t
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (g.isAux_iff.mpr ⟨fun i hi => h1 ⟨i, hi⟩, fun t ht => h2 ⟨t, ht⟩⟩))

theorem IsAux.ne_lit {g : Gadget V} {v : V} (h : g.IsAux v) (i : Fin 3) : v ≠ g.lit i := h.1 i

theorem IsAux.ne_anchor {g : Gadget V} {v : V} (h : g.IsAux v) (t : Fin 3) :
    v ≠ g.anchor t := (g.isAux_iff.mp h).2 t

-- ------------------------------------------------------------- the action

theorem ρ_one (v : V) : g.ρ 1 v = v := by
  rw [map_one]
  rfl

theorem ρ_mul (σ τ : Equiv.Perm (Fin 3)) (v : V) : g.ρ (σ * τ) v = g.ρ σ (g.ρ τ v) := by
  rw [map_mul]
  rfl

theorem ρ_inv_ρ (σ : Equiv.Perm (Fin 3)) (v : V) : g.ρ σ⁻¹ (g.ρ σ v) = v := by
  rw [← g.ρ_mul, inv_mul_cancel, g.ρ_one]

theorem ρ_ρ_inv (σ : Equiv.Perm (Fin 3)) (v : V) : g.ρ σ (g.ρ σ⁻¹ v) = v := by
  rw [← g.ρ_mul, mul_inv_cancel, g.ρ_one]

theorem ρ_injective (σ : Equiv.Perm (Fin 3)) : Function.Injective (g.ρ σ) :=
  (g.ρ σ).injective

/-- Each `g.ρ σ` is an automorphism of the graph. -/
theorem adj_ρ (σ : Equiv.Perm (Fin 3)) {u v : V} :
    g.G.Adj (g.ρ σ u) (g.ρ σ v) ↔ g.G.Adj u v :=
  (g.ρ σ).map_rel_iff

/-- The automorphisms map auxiliary vertices to auxiliary vertices. -/
theorem isAux_map (σ : Equiv.Perm (Fin 3)) {v : V} (h : g.IsAux v) : g.IsAux (g.ρ σ v) := by
  refine g.isAux_iff.mpr ⟨fun i hi => ?_, fun t ht => ?_⟩
  · have h1 : g.ρ σ v = g.ρ σ (g.lit (σ⁻¹ i)) := by
      rw [hi, g.ρ_lit]
      simp
    exact h.1 _ (g.ρ_injective σ h1)
  · exact h.ne_anchor t (g.ρ_injective σ (ht.trans (g.ρ_anchor' σ t).symm))

theorem ρ_eq_anchor (σ : Equiv.Perm (Fin 3)) {u : V} (t : Fin 3) :
    g.ρ σ u = g.anchor t ↔ u = g.anchor t := by
  constructor
  · intro h
    exact g.ρ_injective σ (h.trans (g.ρ_anchor' σ t).symm)
  · intro h
    rw [h, g.ρ_anchor']

/-- Two permutations `σ` and `τ` move `v` to the same vertex exactly when
    `τ⁻¹ * σ` fixes `v`. -/
theorem ρ_eq_ρ_iff (σ τ : Equiv.Perm (Fin 3)) (v : V) :
    g.ρ σ v = g.ρ τ v ↔ g.ρ (τ⁻¹ * σ) v = v := by
  rw [g.ρ_mul]
  constructor
  · intro h
    rw [h, g.ρ_inv_ρ]
  · intro h
    have h2 := congrArg (g.ρ τ) h
    rwa [g.ρ_ρ_inv] at h2

-- ------------------------------------------------------ colorings, inputs

/-- A proper 3-coloring with the anchors colored T, F, B and the literals
    colored by the input `α`. `g.Extends α` says that one exists. -/
def IsColoring (α : Fin 3 → Bool) (c : V → Fin 3) : Prop :=
  (∀ u v, g.G.Adj u v → c u ≠ c v) ∧ c g.gT = 0 ∧ c g.gF = 1 ∧ c g.gB = 2 ∧
    ∀ i, c (g.lit i) = if α i then 0 else 1

theorem extends_iff (α : Fin 3 → Bool) : g.Extends α ↔ ∃ c, g.IsColoring α c := Iff.rfl

variable {g}

theorem IsColoring.proper {α : Fin 3 → Bool} {c : V → Fin 3} (h : g.IsColoring α c)
    {u v : V} (huv : g.G.Adj u v) : c u ≠ c v := h.1 u v huv

theorem IsColoring.anchor {α : Fin 3 → Bool} {c : V → Fin 3} (h : g.IsColoring α c)
    (t : Fin 3) : c (g.anchor t) = t := by
  fin_cases t
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem IsColoring.lit_true {α : Fin 3 → Bool} {c : V → Fin 3} (h : g.IsColoring α c)
    {i : Fin 3} (hi : α i = true) : c (g.lit i) = 0 := by
  have h1 := h.2.2.2.2 i
  rwa [if_pos hi] at h1

theorem IsColoring.lit_false {α : Fin 3 → Bool} {c : V → Fin 3} (h : g.IsColoring α c)
    {i : Fin 3} (hi : α i = false) : c (g.lit i) = 1 := by
  have h1 := h.2.2.2.2 i
  rwa [hi] at h1

/-- A coloring is given by its properness, its values on the anchors and
    its values on the literals. -/
theorem IsColoring.mk' {α : Fin 3 → Bool} {c : V → Fin 3}
    (hp : ∀ u v, g.G.Adj u v → c u ≠ c v) (ha : ∀ t, c (g.anchor t) = t)
    (hl : ∀ i, c (g.lit i) = if α i then 0 else 1) : g.IsColoring α c :=
  ⟨hp, ha 0, ha 1, ha 2, hl⟩

variable (g)

/-- The input (T, T, T). -/
def allTrue : Fin 3 → Bool := fun _ => true

/-- The input (F, F, F). -/
def allFalse : Fin 3 → Bool := fun _ => false

/-- The input with literal `k` true and the other two false. `onlyTrue 2`
    is (F, F, T). -/
def onlyTrue (k : Fin 3) : Fin 3 → Bool := fun i => decide (i = k)

variable {g}

/-- A valid gadget accepts every input with a true literal. -/
theorem Valid.of_true (hv : g.Valid) {α : Fin 3 → Bool} {i : Fin 3} (h : α i = true) :
    ∃ c, g.IsColoring α c := (hv α).mpr ⟨i, h⟩

theorem Valid.allTrue (hv : g.Valid) : ∃ c, g.IsColoring allTrue c := hv.of_true (i := 0) rfl

theorem Valid.onlyTrue (hv : g.Valid) (k : Fin 3) : ∃ c, g.IsColoring (onlyTrue k) c :=
  hv.of_true (i := k) (by simp [Gadget.onlyTrue])

/-- A valid gadget rejects (F, F, F). -/
theorem Valid.not_allFalse (hv : g.Valid) {c : V → Fin 3} : ¬ g.IsColoring allFalse c := by
  intro h
  obtain ⟨i, hi⟩ := (hv _).mp ⟨c, h⟩
  exact Bool.noConfusion hi

variable (g)

-- ------------------------------------------------- the standing assumption

/-- The standing assumption of Section IV-A: no edge joins a literal to G_T
    or to G_F. -/
def NoLitAnchor : Prop := ∀ i, ¬ g.G.Adj (g.lit i) g.gT ∧ ¬ g.G.Adj (g.lit i) g.gF

variable {g}

/-- An edge from one literal to an anchor gives the edges from all literals
    to that anchor. -/
theorem adj_lit_anchor_all {i : Fin 3} {t : Fin 3} (h : g.G.Adj (g.lit i) (g.anchor t))
    (j : Fin 3) : g.G.Adj (g.lit j) (g.anchor t) := by
  have h1 := (g.adj_ρ (Equiv.swap i j)).mpr h
  rwa [g.ρ_lit, Equiv.swap_apply_left, g.ρ_anchor'] at h1

/-- A valid gadget has no edge between a literal and G_T or G_F: by symmetry
    such an edge joins the anchor to all three literals, and then (T, T, T)
    or (F, F, T) is rejected. -/
theorem Valid.noLitAnchor (hv : g.Valid) : g.NoLitAnchor := by
  intro i
  constructor
  · intro h
    obtain ⟨c, hc⟩ := hv.allTrue
    have h0 : c (g.lit i) = 0 := hc.lit_true rfl
    exact hc.proper h (h0.trans hc.2.1.symm)
  · intro h
    have h0 : g.G.Adj (g.lit 0) (g.anchor 1) := adj_lit_anchor_all (t := 1) h 0
    obtain ⟨c, hc⟩ := hv.onlyTrue 2
    have h1 : c (g.lit 0) = 1 := hc.lit_false (by decide)
    exact hc.proper h0 (h1.trans (hc.anchor 1).symm)

/-- Under the standing assumption, an anchor adjacent to a literal is G_B. -/
theorem NoLitAnchor.eq_two (h : g.NoLitAnchor) {i t : Fin 3}
    (hadj : g.G.Adj (g.lit i) (g.anchor t)) : t = 2 := by
  fin_cases t
  · exact absurd hadj (h i).1
  · exact absurd hadj (h i).2
  · rfl

-- ------------------------------------------------------------ recoloring

/-- To check that a recoloring is proper, it suffices to look at the edges
    with an end among the recolored vertices `S`. -/
theorem proper_of_agree {c c' : V → Fin 3} (S : V → Prop)
    (hc : ∀ u v, g.G.Adj u v → c u ≠ c v) (hagree : ∀ v, ¬ S v → c' v = c v)
    (hS : ∀ u v, S u → g.G.Adj u v → c' u ≠ c' v) :
    ∀ u v, g.G.Adj u v → c' u ≠ c' v := by
  intro u v huv
  by_cases hu : S u
  · exact hS u v hu huv
  by_cases hv : S v
  · exact (hS v u hv huv.symm).symm
  · rw [hagree u hu, hagree v hv]
    exact hc u v huv

open Classical in
/-- Recolor the vertices `f i` with the colors `val i` and keep `c`
    elsewhere. -/
noncomputable def recolor {ι : Type} (c : V → Fin 3) (f : ι → V) (val : ι → Fin 3) :
    V → Fin 3 :=
  fun v => if h : ∃ i, f i = v then val (Classical.choose h) else c v

theorem recolor_apply {ι : Type} (c : V → Fin 3) {f : ι → V} (hf : Function.Injective f)
    (val : ι → Fin 3) (i : ι) : recolor c f val (f i) = val i := by
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  unfold recolor
  rw [dif_pos h, hf (Classical.choose_spec h)]

theorem recolor_of_ne {ι : Type} (c : V → Fin 3) {f : ι → V} (val : ι → Fin 3) {v : V}
    (h : ∀ i, f i ≠ v) : recolor c f val v = c v := by
  unfold recolor
  rw [dif_neg (fun ⟨i, hi⟩ => h i hi)]

-- --------------------------------------------------------------- counting

variable (g)

/-- Distinct auxiliary vertices indexed by `ι` give a lower bound on the
    number of auxiliary vertices. -/
theorem card_aux_ge [Finite V] {ι : Type} [Fintype ι] (f : ι → V)
    (hinj : Function.Injective f) (haux : ∀ i, g.IsAux (f i)) :
    Fintype.card ι ≤ Nat.card {v // g.IsAux v} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective (fun i => (⟨f i, haux i⟩ : {v // g.IsAux v}))
    (fun i j h => hinj (congrArg Subtype.val h))

/-- If as many distinct auxiliary vertices are listed as there are, the list
    is complete. -/
theorem aux_surj [Finite V] {ι : Type} [Fintype ι] (f : ι → V)
    (hinj : Function.Injective f) (haux : ∀ i, g.IsAux (f i))
    (hcard : Nat.card {v // g.IsAux v} ≤ Fintype.card ι) :
    ∀ v, g.IsAux v → ∃ i, f i = v := by
  have hinj' : Function.Injective (fun i => (⟨f i, haux i⟩ : {v // g.IsAux v})) :=
    fun i j h => hinj (congrArg Subtype.val h)
  have hbij := hinj'.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card (α := ι)]
    exact hcard)
  intro v hv
  obtain ⟨i, hi⟩ := hbij.2 ⟨v, hv⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- The six fixed vertices: the literals and the anchors. -/
def named : Fin 3 ⊕ Fin 3 → V := Sum.elim g.lit g.anchor

theorem named_injective : Function.Injective g.named := by
  intro r r' h
  rcases r with i | s <;> rcases r' with i' | s'
  · exact congrArg Sum.inl (g.lit_inj h)
  · exact absurd h (g.lit_ne_anchor' i s')
  · exact absurd h.symm (g.lit_ne_anchor' i' s)
  · exact congrArg Sum.inr (g.anchor_injective h)

/-- Every vertex is an auxiliary vertex or one of the six fixed ones. -/
theorem sum_bijective :
    Function.Bijective (Sum.elim (Subtype.val : {v // g.IsAux v} → V) g.named) := by
  constructor
  · intro x y h
    rcases x with a | r <;> rcases y with b | r'
    · exact congrArg Sum.inl (Subtype.ext h)
    · rcases r' with i | t
      · exact absurd h (a.2.ne_lit i)
      · exact absurd h (a.2.ne_anchor t)
    · rcases r with i | t
      · exact absurd h.symm (b.2.ne_lit i)
      · exact absurd h.symm (b.2.ne_anchor t)
    · exact congrArg Sum.inr (g.named_injective h)
  · intro v
    rcases g.vertex_cases v with ⟨i, rfl⟩ | ⟨t, rfl⟩ | hv
    · exact ⟨.inr (.inl i), rfl⟩
    · exact ⟨.inr (.inr t), rfl⟩
    · exact ⟨.inl ⟨v, hv⟩, rfl⟩

/-- The number of vertices is the number of auxiliary vertices plus six. -/
theorem card_eq [Finite V] : Nat.card V = Nat.card {v // g.IsAux v} + 6 := by
  have h3 : Nat.card (Fin 3) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← Nat.card_congr (Equiv.ofBijective _ g.sum_bijective), Nat.card_sum, Nat.card_sum, h3]

end Gadget

end Def1
