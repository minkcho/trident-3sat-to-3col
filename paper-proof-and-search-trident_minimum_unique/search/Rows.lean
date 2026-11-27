import search.Space
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card

/-!
  The rows of the judge, in the terms of Definition 1.

  The judge tests a candidate on eight rows, one for each input. Bit `i` of
  the row number `env` says whether literal `i` is true (`envInput`), and
  every choice of three truth values is a row (`exists_env`). The pins of a
  row fix the colors of the anchors and of the literals
  (`rowPins_mem_iff`).
-/

namespace Def1

open Atlas

/-- The literal coloring that the engine's input `env` encodes. -/
def envInput (env : Nat) : Fin 3 → Bool := fun i => env >>> i.val &&& 1 == 1

/-- Check of the encoding: an input below 8 has a true literal exactly when
    it is not 0. -/
theorem envInput_some_true : ∀ env, env < 8 →
    ((∃ i : Fin 3, envInput env i = true) ↔ env ≠ 0) := by decide

/-- The pins of the row `env`, for any composition: the anchors are pinned
    to T, F, B (0, 1, 2) and literal `i` to T or F according to the input. -/
theorem rowPins_mem_iff {parts : List Nat} {env : Nat} {w : Vertex} {c : Nat} :
    (w, c) ∈ rowPins parts env ↔
      (w = .aux parts.length 0 ∧ c = 0) ∨ (w = .aux (parts.length + 1) 0 ∧ c = 1) ∨
      (w = .aux (parts.length + 2) 0 ∧ c = 2) ∨
      ∃ i : Fin 3, w = .lit i.val ∧ c = if envInput env i then 0 else 1 := by
  rw [rowPins_eq]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro (((h | h | h) | ⟨v, hv, rfl, rfl⟩) | ⟨v, hv, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨i, hi, hbit, rfl⟩ := mem_selected.mp hv
      refine Or.inr (Or.inr (Or.inr ⟨⟨i, hi⟩, rfl, ?_⟩))
      show 0 = if (env >>> i &&& 1 == 1) = true then 0 else 1
      rw [if_pos hbit]
    · obtain ⟨i, hi, hbit, rfl⟩ := mem_forbidden.mp hv
      refine Or.inr (Or.inr (Or.inr ⟨⟨i, hi⟩, rfl, ?_⟩))
      show 1 = if (env >>> i &&& 1 == 1) = true then 0 else 1
      rw [hbit]
      rfl
  · rintro (h | h | h | ⟨i, rfl, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
    · by_cases hb : envInput env i = true
      · exact Or.inl (Or.inr ⟨.lit i.val, mem_selected.mpr ⟨i.val, i.isLt, hb, rfl⟩,
          rfl, by rw [if_pos hb]⟩)
      · exact Or.inr ⟨.lit i.val,
          mem_forbidden.mpr ⟨i.val, i.isLt, (Bool.not_eq_true _).mp hb, rfl⟩,
          rfl, by rw [if_neg hb]⟩

theorem colorAt_rowPins_iff {parts : List Nat} {env : Nat} {w : Vertex} {c : Nat} :
    colorAt (rowPins parts env) w = some c ↔
      (w = .aux parts.length 0 ∧ c = 0) ∨ (w = .aux (parts.length + 1) 0 ∧ c = 1) ∨
      (w = .aux (parts.length + 2) 0 ∧ c = 2) ∨
      ∃ i : Fin 3, w = .lit i.val ∧ c = if envInput env i then 0 else 1 :=
  ⟨fun h => rowPins_mem_iff.mp (mem_of_colorAt_eq_some h),
   fun h => colorAt_eq_some_of_mem (rowPins_keys_nodup parts env) (rowPins_mem_iff.mpr h)⟩

/-- A color that respects the pins is the pinned value. -/
theorem pinOk_eq {pins : List (Vertex × Nat)} {w : Vertex} {x c : Nat}
    (hp : pinOk pins w x) (hc : colorAt pins w = some c) : x = c := by
  unfold pinOk at hp
  rw [hc] at hp
  exact hp

/-- Check of the encoding: every choice of three truth values is the input
    of a row. -/
theorem exists_env_bits : ∀ a0 a1 a2 : Bool, ∃ env, env < 8 ∧
    envInput env 0 = a0 ∧ envInput env 1 = a1 ∧ envInput env 2 = a2 := by decide

theorem exists_env (α : Fin 3 → Bool) : ∃ env, env < 8 ∧ envInput env = α := by
  obtain ⟨env, henv, h0, h1, h2⟩ := exists_env_bits (α 0) (α 1) (α 2)
  refine ⟨env, henv, ?_⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end Def1
