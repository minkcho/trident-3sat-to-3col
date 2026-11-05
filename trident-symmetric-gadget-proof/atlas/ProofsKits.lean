import atlas.Kits
/-!
  Reflection theorems for the kit enumerators -- failure mode (3), "judging
  false as true" (and its twin, missing a true optimum). What is proved,
  for every input:

  * the mask enumeration is exactly the sublists of the free vertices
    (`bitSubset_sublist` + `exists_bitSubset`) -- nothing else is scored,
    and nothing is skipped;
  * the bit lemmas behind it (`bit_eq_testBit`, `exists_env_of_bits`),
    which the multi-clause layer uses to read assignments as bits.

  (The full line also reflects the min/max subset enumerators of the
  other problems' kits here.)
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

theorem twoMul_and_one (m : Nat) : (2 * m) &&& 1 = 0 := by
  simp [Nat.and_one_is_mod, Nat.mul_mod_right]

theorem twoMulAdd_and_one (m : Nat) : (2 * m + 1) &&& 1 = 1 := by
  simp [Nat.and_one_is_mod]

theorem shiftRight_one_eq (n : Nat) : n >>> 1 = n / 2 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, Nat.shiftRight_succ, Nat.shiftRight_zero]

/-- The framework's bit test is `Nat.testBit`. -/
theorem bit_eq_testBit (x v : Nat) : (x >>> v &&& 1 == 1) = x.testBit v := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  by_cases h : x / 2 ^ v % 2 = 1 <;> simp [h]

/-- Every Boolean pattern on `n` bits is realized by some `env < 2^n`. -/
theorem exists_env_of_bits (b : Nat → Bool) :
    ∀ n, ∃ env, env < 2 ^ n ∧ ∀ v, v < n → env.testBit v = b v := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp, fun v hv => absurd hv (Nat.not_lt_zero v)⟩
  | succ n ih =>
    obtain ⟨env, hlt, hbits⟩ := ih
    refine ⟨(if b n then 2 ^ n else 0) + env, ?_, ?_⟩
    · rw [Nat.pow_succ]
      split <;> omega
    · intro v hv
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with hv | rfl
      · split
        · rw [Nat.testBit_two_pow_add_gt hv]
          exact hbits v hv
        · rw [Nat.zero_add]
          exact hbits v hv
      · split
        · rename_i hb
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hb]
          rfl
        · rename_i hb
          rw [Nat.zero_add, Nat.testBit_lt_two_pow hlt]
          simp only [Bool.not_eq_true] at hb
          exact hb.symm

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
