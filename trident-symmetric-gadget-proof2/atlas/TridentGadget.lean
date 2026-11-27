import atlas.Definition1
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite

/-!
  The trident is a valid S3-symmetric clause gadget in the sense of
  Definition 1 (`Definition1.lean`): `tridentGadget` and
  `tridentGadget_valid`. Mathlib only; the search engine is not used.
-/

namespace Def1

instance : DecidableRel tridentEdge := fun a b => by
  cases a <;> cases b <;> simp only [tridentEdge] <;> infer_instance

instance : DecidableRel trident.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj tridentEdge a b).symm

/-- A permutation of the indices acts on the trident's vertices. -/
def tridentMap (σ : Equiv.Perm (Fin 3)) : TV → TV
  | .x i => .x (σ i)
  | .p i => .p (σ i)
  | .u i => .u (σ i)
  | .gT => .gT
  | .gF => .gF
  | .gB => .gB

theorem tridentMap_one (v : TV) : tridentMap 1 v = v := by cases v <;> rfl

theorem tridentMap_mul (σ τ : Equiv.Perm (Fin 3)) (v : TV) :
    tridentMap (σ * τ) v = tridentMap σ (tridentMap τ v) := by cases v <;> rfl

def tridentEquiv (σ : Equiv.Perm (Fin 3)) : TV ≃ TV where
  toFun := tridentMap σ
  invFun := tridentMap σ⁻¹
  left_inv v := by rw [← tridentMap_mul, inv_mul_cancel, tridentMap_one]
  right_inv v := by rw [← tridentMap_mul, mul_inv_cancel, tridentMap_one]

theorem tridentEdge_map (σ : Equiv.Perm (Fin 3)) (a b : TV) :
    tridentEdge (tridentMap σ a) (tridentMap σ b) ↔ tridentEdge a b := by
  cases a <;> cases b <;> simp [tridentEdge, tridentMap]

/-- The action is by automorphisms of the trident. -/
def tridentIso (σ : Equiv.Perm (Fin 3)) : trident ≃g trident where
  toEquiv := tridentEquiv σ
  map_rel_iff' := by
    intro a b
    show trident.Adj (tridentMap σ a) (tridentMap σ b) ↔ trident.Adj a b
    have hne : tridentMap σ a ≠ tridentMap σ b ↔ a ≠ b := (tridentEquiv σ).injective.ne_iff
    simp only [trident, SimpleGraph.fromRel_adj, tridentEdge_map, hne]

/-- The trident as a gadget of Definition 1. -/
def tridentGadget : Gadget TV where
  G := trident
  lit := TV.x
  gT := TV.gT
  gF := TV.gF
  gB := TV.gB
  lit_inj := fun _ _ h => TV.x.inj h
  lit_ne_anchor := fun _ => ⟨by simp, by simp, by simp⟩
  lit_nonadj := fun i j => by simp [trident, tridentEdge]
  palette := by simp [trident, tridentEdge]
  fan := fun i => by simp [trident, tridentEdge]
  ρ :=
    { toFun := tridentIso
      map_one' := RelIso.ext fun v => tridentMap_one v
      map_mul' := fun σ τ => RelIso.ext fun v => tridentMap_mul σ τ v }
  ρ_lit := fun _ _ => rfl
  ρ_anchor := fun _ => ⟨rfl, rfl, rfl⟩

/-- The coloring used for a satisfying input: `i0` is a true literal. -/
def tridentColoring (α : Fin 3 → Bool) (i0 : Fin 3) : TV → Fin 3
  | .x i => if α i then 0 else 1
  | .p i => if i = i0 then 1 else 2
  | .u i => if i = i0 then 2 else if i = i0 + 1 then 0 else 1
  | .gT => 0
  | .gF => 1
  | .gB => 2

theorem tridentColoring_proper : ∀ (a0 a1 a2 : Bool) (i0 : Fin 3),
    ![a0, a1, a2] i0 = true → ∀ u v : TV, trident.Adj u v →
      tridentColoring ![a0, a1, a2] i0 u ≠ tridentColoring ![a0, a1, a2] i0 v := by
  decide

/-- Theorem 4 of the paper in the terms of Definition 1: a coloring of the
    three literals extends to a proper coloring of the trident exactly when
    it satisfies the clause. -/
theorem tridentGadget_valid : tridentGadget.Valid := by
  intro α
  constructor
  · rintro ⟨c, hc, hT, hF, hB, hlit⟩
    by_contra hno
    have hfalse : ∀ i, α i = false := fun i => by
      cases h : α i
      · rfl
      · exact absurd ⟨i, h⟩ hno
    have hx : ∀ i, c (TV.x i) = 1 := fun i => by
      have := hlit i
      rw [hfalse i] at this
      exact this
    have key1 : ∀ y : Fin 3, (1 : Fin 3) ≠ y → y ≠ 0 → y = 2 := by decide
    have hp : ∀ i, c (TV.p i) = 2 := fun i => by
      have h1 : c (TV.x i) ≠ c (TV.p i) :=
        hc _ _ (by simp [tridentGadget, trident, tridentEdge])
      have h2 : c (TV.p i) ≠ c TV.gT :=
        hc _ _ (by simp [tridentGadget, trident, tridentEdge])
      rw [hx i] at h1
      exact key1 _ h1 (fun h => h2 (h.trans hT.symm))
    have hu : ∀ i, c (TV.u i) ≠ 2 := fun i => by
      have h1 : c (TV.p i) ≠ c (TV.u i) :=
        hc _ _ (by simp [tridentGadget, trident, tridentEdge])
      rw [hp i] at h1
      exact fun h => h1 h.symm
    have h01 : c (TV.u 0) ≠ c (TV.u 1) :=
      hc _ _ (by simp [tridentGadget, trident, tridentEdge])
    have h02 : c (TV.u 0) ≠ c (TV.u 2) :=
      hc _ _ (by simp [tridentGadget, trident, tridentEdge])
    have h12 : c (TV.u 1) ≠ c (TV.u 2) :=
      hc _ _ (by simp [tridentGadget, trident, tridentEdge])
    have key2 : ∀ a b d : Fin 3, a ≠ 2 → b ≠ 2 → d ≠ 2 → a ≠ b → a ≠ d → b ≠ d → False := by
      decide
    exact key2 _ _ _ (hu 0) (hu 1) (hu 2) h01 h02 h12
  · rintro ⟨i0, hi0⟩
    have hα : α = ![α 0, α 1, α 2] := by
      funext i
      fin_cases i <;> rfl
    refine ⟨tridentColoring α i0, ?_, rfl, rfl, rfl, fun i => rfl⟩
    intro u v huv
    rw [hα]
    exact tridentColoring_proper (α 0) (α 1) (α 2) i0 (by rw [← hα]; exact hi0) u v huv

theorem card_TV : Fintype.card TV = 12 := by decide

instance : DecidablePred tridentGadget.IsAux := fun v => by
  unfold Gadget.IsAux
  infer_instance

/-- The trident has six auxiliary vertices: the `p i` and the `u i`. -/
theorem tridentGadget_card_aux : Nat.card {v // tridentGadget.IsAux v} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

end Def1
