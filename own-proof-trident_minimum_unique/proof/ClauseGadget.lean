import proof.Basics

/-!
  # Lemma 11 for arbitrary clause gadgets

  The proof of Lemma 11 in the paper ends with a remark: the argument does
  not rely on S3-symmetry and therefore holds for arbitrary clause gadgets.
  This file proves the lemma in that generality. A `ClauseGadget` is the
  graph of Definition 1 without the action.

  The argument recolors the literals with F, so it needs that no edge joins
  a literal to G_F. `Gadget.Valid.noLitAnchor` excludes the edges between a
  literal and G_T or G_F by the symmetry of the gadget. Here they are
  excluded without symmetry (`ClauseGadget.noLitAnchor`): an edge from a
  literal to G_T rejects the input in which only this literal is true, and
  an edge from a literal to G_F rejects a satisfying input in which this
  literal is false.
-/

namespace Def1

variable {V : Type}

/-- A clause gadget for 3-coloring without a symmetry requirement: a simple
    graph with three pairwise non-adjacent literal vertices, a palette
    triangle `gT`, `gF`, `gB` with `gB` adjacent to every literal, and any
    other vertices. This is Definition 1 without the action. -/
structure ClauseGadget (V : Type) where
  G : SimpleGraph V
  lit : Fin 3 → V
  gT : V
  gF : V
  gB : V
  lit_inj : Function.Injective lit
  lit_ne_anchor : ∀ i, lit i ≠ gT ∧ lit i ≠ gF ∧ lit i ≠ gB
  lit_nonadj : ∀ i j, ¬ G.Adj (lit i) (lit j)
  palette : G.Adj gT gF ∧ G.Adj gF gB ∧ G.Adj gB gT
  fan : ∀ i, G.Adj gB (lit i)

/-- An auxiliary vertex of a clause gadget: neither a literal nor an
    anchor. -/
def ClauseGadget.IsAux (C : ClauseGadget V) (v : V) : Prop :=
  (∀ i, v ≠ C.lit i) ∧ v ≠ C.gT ∧ v ≠ C.gF ∧ v ≠ C.gB

/-- The input `α` extends to a proper 3-coloring with the anchors colored
    T, F, B, as in Definition 1. -/
def ClauseGadget.Extends (C : ClauseGadget V) (α : Fin 3 → Bool) : Prop :=
  ∃ c : V → Fin 3, (∀ u v, C.G.Adj u v → c u ≠ c v) ∧
    c C.gT = 0 ∧ c C.gF = 1 ∧ c C.gB = 2 ∧
    ∀ i, c (C.lit i) = if α i then 0 else 1

/-- Validity, as in Definition 1: exactly the inputs with a true literal
    extend. -/
def ClauseGadget.Valid (C : ClauseGadget V) : Prop :=
  ∀ α : Fin 3 → Bool, C.Extends α ↔ ∃ i, α i = true

/-- A gadget of Definition 1 is a clause gadget: forget the action. -/
def Gadget.toClauseGadget (g : Gadget V) : ClauseGadget V where
  G := g.G
  lit := g.lit
  gT := g.gT
  gF := g.gF
  gB := g.gB
  lit_inj := g.lit_inj
  lit_ne_anchor := g.lit_ne_anchor
  lit_nonadj := g.lit_nonadj
  palette := g.palette
  fan := g.fan

/-- Validity and the auxiliary vertices of a gadget of Definition 1 do not
    mention its action: they are those of the clause gadget. -/
theorem Gadget.toClauseGadget_spec (g : Gadget V) :
    (g.toClauseGadget.Valid ↔ g.Valid) ∧ ∀ v, g.toClauseGadget.IsAux v ↔ g.IsAux v :=
  ⟨Iff.rfl, fun _ => Iff.rfl⟩

namespace ClauseGadget

variable (C : ClauseGadget V)

/-- The standing assumption of Section IV-A, without symmetry. In a valid
    clause gadget no edge joins a literal to G_T or to G_F: an edge to G_T
    rejects the input in which only this literal is true, and an edge to G_F
    rejects an input in which this literal is false and another literal is
    true. -/
theorem noLitAnchor (hv : C.Valid) (i : Fin 3) :
    ¬ C.G.Adj (C.lit i) C.gT ∧ ¬ C.G.Adj (C.lit i) C.gF := by
  constructor
  · intro hadj
    have htrue : Gadget.onlyTrue i i = true := decide_eq_true rfl
    obtain ⟨c, hp, hT, -, -, hl⟩ := (hv (Gadget.onlyTrue i)).mpr ⟨i, htrue⟩
    have h1 : c (C.lit i) = 0 := by
      have h := hl i
      rwa [if_pos htrue] at h
    exact hp _ _ hadj (h1.trans hT.symm)
  · intro hadj
    have hother : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i := by decide
    obtain ⟨j, hji⟩ := hother i
    have htrue : Gadget.onlyTrue j j = true := decide_eq_true rfl
    have hfalse : Gadget.onlyTrue j i = false := decide_eq_false fun h => hji h.symm
    obtain ⟨c, hp, -, hF, -, hl⟩ := (hv (Gadget.onlyTrue j)).mpr ⟨j, htrue⟩
    have h1 : c (C.lit i) = 1 := by
      have h := hl i
      rwa [hfalse] at h
    exact hp _ _ hadj (h1.trans hF.symm)

/-- Lemma 11 for arbitrary clause gadgets (the remark at the end of its
    proof). A valid clause gadget, with or without symmetry, has an
    auxiliary vertex that is adjacent to exactly one literal. Otherwise a
    proper coloring for (F, F, T) stays proper when the literals are
    recolored with F, and (F, F, F) is accepted. -/
theorem lemma11 (hv : C.Valid) :
    ∃ v, C.IsAux v ∧ ∃ k : Fin 3, ∀ j, C.G.Adj v (C.lit j) ↔ j = k := by
  by_contra hno
  -- a proper coloring for (F, F, T)
  have htrue : Gadget.onlyTrue 2 2 = true := decide_eq_true rfl
  obtain ⟨c, hp, hT, hF, hB, hl⟩ := (hv (Gadget.onlyTrue 2)).mpr ⟨2, htrue⟩
  have hx : ∀ j : Fin 3, j ≠ 2 → c (C.lit j) = 1 := by
    intro j hj
    have hfalse : Gadget.onlyTrue 2 j = false := decide_eq_false hj
    have h := hl j
    rwa [hfalse] at h
  -- no neighbor of a literal, other than a literal, has the color F
  have key : ∀ i v, (∀ j, v ≠ C.lit j) → C.G.Adj (C.lit i) v → c v ≠ 1 := by
    intro i v hvl hadj
    by_cases hgT : v = C.gT
    · rw [hgT, hT]
      decide
    by_cases hgF : v = C.gF
    · rw [hgF] at hadj
      exact absurd hadj (C.noLitAnchor hv i).2
    by_cases hgB : v = C.gB
    · rw [hgB, hB]
      decide
    by_cases hi2 : i = 2
    · -- `v` sees `lit 2`; it is not its only literal neighbor, so it sees a false literal
      have hex : ∃ j, j ≠ 2 ∧ C.G.Adj v (C.lit j) := by
        by_contra hnone
        refine hno ⟨v, ⟨hvl, hgT, hgF, hgB⟩, 2, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
        · by_contra hj2
          exact hnone ⟨j, hj2, hj⟩
        · rw [hj, ← hi2]
          exact hadj.symm
      obtain ⟨j, hj2, hj⟩ := hex
      have h1 := hp _ _ hj
      rwa [hx j hj2] at h1
    · have h1 := hp _ _ hadj
      rw [hx i hi2] at h1
      exact fun h => h1 h.symm
  -- recolor the literals with F
  have hlit : ∀ i, Gadget.recolor c C.lit (fun _ => (1 : Fin 3)) (C.lit i) = 1 :=
    fun i => Gadget.recolor_apply c C.lit_inj _ i
  have hne : ∀ v, (∀ i, v ≠ C.lit i) →
      Gadget.recolor c C.lit (fun _ => (1 : Fin 3)) v = c v :=
    fun v hv' => Gadget.recolor_of_ne c _ fun i hi => hv' i hi.symm
  have hext : C.Extends Gadget.allFalse := by
    refine ⟨Gadget.recolor c C.lit (fun _ => 1), ?_, ?_, ?_, ?_, fun i => ?_⟩
    · intro u v huv
      by_cases hu : ∃ i, u = C.lit i
      · obtain ⟨i, rfl⟩ := hu
        rw [hlit i]
        by_cases hv' : ∃ j, v = C.lit j
        · obtain ⟨j, rfl⟩ := hv'
          exact absurd huv (C.lit_nonadj i j)
        · have hvl : ∀ j, v ≠ C.lit j := fun j hj => hv' ⟨j, hj⟩
          rw [hne v hvl]
          exact Ne.symm (key i v hvl huv)
      · have hul : ∀ i, u ≠ C.lit i := fun i hi => hu ⟨i, hi⟩
        rw [hne u hul]
        by_cases hv' : ∃ j, v = C.lit j
        · obtain ⟨j, rfl⟩ := hv'
          rw [hlit j]
          exact key j u hul huv.symm
        · have hvl : ∀ j, v ≠ C.lit j := fun j hj => hv' ⟨j, hj⟩
          rw [hne v hvl]
          exact hp u v huv
    · rw [hne C.gT fun i hi => (C.lit_ne_anchor i).1 hi.symm]
      exact hT
    · rw [hne C.gF fun i hi => (C.lit_ne_anchor i).2.1 hi.symm]
      exact hF
    · rw [hne C.gB fun i hi => (C.lit_ne_anchor i).2.2 hi.symm]
      exact hB
    · rw [hlit i]
      rfl
  obtain ⟨i, hi⟩ := (hv _).mp hext
  exact Bool.noConfusion hi

end ClauseGadget

end Def1
