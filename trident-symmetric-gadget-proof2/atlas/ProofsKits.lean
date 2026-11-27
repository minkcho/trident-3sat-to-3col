import atlas.Kits
/-!
  Reflection of the mask enumeration `bitSubset`: a masked subset is a
  sublist (`bitSubset_sublist`), and every sublist of the free switches is
  the subset of some mask below 2^length (`exists_bitSubset`), so the walk
  scores nothing extra and skips nothing.
-/

namespace Atlas

open List

-- ----------------------------------------------------------------- bitSubset

theorem bitSubset_sublist {α : Type} (mask : Nat) (rest : List α) :
    bitSubset mask rest <+ rest := by
  induction rest generalizing mask with
  | nil => exact Sublist.slnil
  | cons v rest ih =>
    show (if mask &&& 1 == 1 then [v] else []) ++ bitSubset (mask >>> 1) rest
        <+ v :: rest
    by_cases h : mask &&& 1 == 1
    · rw [if_pos h]
      exact Sublist.cons_cons v (ih (mask >>> 1))
    · rw [if_neg h]
      exact Sublist.cons v (ih (mask >>> 1))

theorem shiftRight_one_eq (n : Nat) : n >>> 1 = n / 2 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, Nat.shiftRight_succ, Nat.shiftRight_zero]

theorem twoMul_shift (m : Nat) : (2 * m) >>> 1 = m := by
  rw [shiftRight_one_eq]; omega

theorem twoMulAdd_shift (m : Nat) : (2 * m + 1) >>> 1 = m := by
  rw [shiftRight_one_eq]; omega

/-- Enumeration completeness: every sublist of the free vertices is hit by
    a mask below 2^length. -/
theorem exists_bitSubset {α : Type} {T rest : List α} (h : T <+ rest) :
    ∃ mask, mask < 2 ^ rest.length ∧ bitSubset mask rest = T := by
  induction h with
  | slnil => exact ⟨0, by simp, rfl⟩
  | cons v h ih =>
    obtain ⟨m, hm, hbs⟩ := ih
    refine ⟨2 * m, ?_, ?_⟩
    · simp only [List.length_cons, Nat.pow_succ]
      omega
    · simp [bitSubset, twoMul_shift, hbs]
  | cons_cons v h ih =>
    obtain ⟨m, hm, hbs⟩ := ih
    refine ⟨2 * m + 1, ?_, ?_⟩
    · simp only [List.length_cons, Nat.pow_succ]
      omega
    · simp [bitSubset, twoMulAdd_shift, hbs]

end Atlas
