import atlas.OrbitStructure
import atlas.ProofsAction

/-!
  From Lemma 6 to the engine's labels.

  The engine writes a permutation as its value table (`Atlas.Perm`) and lets
  it act on the `j`-th vertex of a part of size `n` by a fixed formula
  (`Universe.act`; `stdAct` below). This file connects Mathlib's
  `Equiv.Perm (Fin 3)` to the tables (`toTable`) and shows that every orbit
  of an S3 action can be labeled so that the action becomes the engine's
  formula (`exists_engine_labeling`). The orbit types come from
  `orbit_structure` (Lemma 6).

  The `decide` proofs in this file compare the engine's hand-written tables
  of the six permutations (`perms`, `parity`, `pidx`) with the permutations
  themselves; they are checks of data, not of the classification.
-/

namespace Def1

open Atlas MulAction

-- ----------------------------------------------- permutations and tables

/-- The value table of a permutation. -/
def toTable (σ : Equiv.Perm (Fin 3)) : Atlas.Perm :=
  ((σ 0).val, (σ 1).val, (σ 2).val)

theorem app_toTable (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    app (toTable σ) i.val = (σ i).val := by
  fin_cases i <;> rfl

/-- The engine's `compose` is the composition of permutations. -/
theorem toTable_mul (σ τ : Equiv.Perm (Fin 3)) :
    toTable (σ * τ) = compose (toTable σ) (toTable τ) := by
  show ((σ (τ 0)).val, (σ (τ 1)).val, (σ (τ 2)).val)
    = (app (toTable σ) (τ 0).val, app (toTable σ) (τ 1).val, app (toTable σ) (τ 2).val)
  rw [app_toTable, app_toTable, app_toTable]

theorem toTable_injective : Function.Injective toTable := by
  intro σ τ h
  have h0 : (σ 0).val = (τ 0).val := congrArg (fun t : Atlas.Perm => t.1) h
  have h1 : (σ 1).val = (τ 1).val := congrArg (fun t : Atlas.Perm => t.2.1) h
  have h2 : (σ 2).val = (τ 2).val := congrArg (fun t : Atlas.Perm => t.2.2) h
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Table check: the list `perms` contains the table of every permutation. -/
theorem toTable_mem : ∀ σ : Equiv.Perm (Fin 3), toTable σ ∈ perms := by decide

/-- Table check: every entry of `perms` is the table of a permutation. -/
theorem toTable_surj : ∀ s ∈ perms, ∃ σ : Equiv.Perm (Fin 3), toTable σ = s := by
  decide

/-- Table check: the engine's `parity` is 0 on the even permutations and 1
    on the odd ones. -/
theorem parity_toTable : ∀ σ : Equiv.Perm (Fin 3),
    parity (toTable σ) = if Equiv.Perm.sign σ = 1 then 0 else 1 := by decide

/-- Table check: `pidx` is an index into the six-element list `perms`. -/
theorem pidx_lt : ∀ s ∈ perms, pidx s < 6 := by decide

theorem pidx_injective {s t : Atlas.Perm} (hs : s ∈ perms) (ht : t ∈ perms)
    (h : pidx s = pidx t) : s = t := by
  rw [← pidx_getD s hs, ← pidx_getD t ht, h]

-- ------------------------------------------------ the engine's label action

/-- The engine's action on the `j`-th vertex of a part of size `n`
    (`Universe.act`): fixed, sign, natural, or regular. -/
def stdAct (n : Nat) (s : Atlas.Perm) (j : Nat) : Nat :=
  match n with
  | 1 => j
  | 2 => j ^^^ parity s
  | 3 => app s j
  | _ => pidx (compose s (perms.getD j (0, 1, 2)))

theorem act_aux_std (U : Universe) (s : Atlas.Perm) (p j : Nat) :
    U.act s (.aux p j) = .aux p (stdAct (U.size p) s j) := by
  rcases hsz : U.size p with _ | _ | _ | _ | m
  · exact act_aux_reg s j (Or.inl hsz)
  · exact act_aux_one s j hsz
  · exact act_aux_two s j hsz
  · exact act_aux_three s j hsz
  · exact act_aux_reg s j (Or.inr (by omega))

/-- Moving `a` by `σ` and by `τ` gives the same point exactly when `τ⁻¹ σ`
    fixes `a`. -/
theorem smul_eq_smul_iff {G X : Type*} [Group G] [MulAction G X] (a : X) (σ τ : G) :
    σ • a = τ • a ↔ (τ⁻¹ * σ) • a = a := by
  rw [mul_smul, inv_smul_eq_iff]

/-- Every orbit of an S3 action can be labeled by `0, …, n - 1`, with `n`
    the size of the orbit and `n ∈ {1, 2, 3, 6}`, so that the action on the
    labels is the engine's formula for a part of size `n`. -/
theorem exists_engine_labeling {X : Type*} [MulAction (Equiv.Perm (Fin 3)) X] (a : X) :
    ∃ n, (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) ∧
      Nat.card (orbit (Equiv.Perm (Fin 3)) a) = n ∧
      ∃ lab : X → Nat,
        (∀ x ∈ orbit (Equiv.Perm (Fin 3)) a, lab x < n) ∧
        (∀ x ∈ orbit (Equiv.Perm (Fin 3)) a, ∀ y ∈ orbit (Equiv.Perm (Fin 3)) a,
          lab x = lab y → x = y) ∧
        (∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ orbit (Equiv.Perm (Fin 3)) a,
          lab (σ • x) = stdAct n (toTable σ) (lab x)) := by
  rcases orbit_structure a with ⟨hc, hfix⟩ | ⟨hc, hfix⟩ | ⟨hc, k, hfix⟩ | ⟨hc, hfix⟩
  · -- size 1: the fixed vertex
    obtain ⟨lab, hlab, hinj⟩ := exists_orbit_labeling a (fun _ : Equiv.Perm (Fin 3) => 0)
      (fun σ τ => by simp [hfix σ, hfix τ])
    refine ⟨1, Or.inl rfl, hc, lab, ?_, hinj, ?_⟩
    · rintro x ⟨σ, rfl⟩
      show lab (σ • a) < 1
      rw [hlab]
      exact Nat.one_pos
    · rintro ρ x ⟨σ, rfl⟩
      show lab (ρ • σ • a) = stdAct 1 (toTable ρ) (lab (σ • a))
      rw [← mul_smul, hlab, hlab]
      rfl
  · -- size 2: the sign action
    obtain ⟨lab, hlab, hinj⟩ := exists_orbit_labeling a
      (fun σ : Equiv.Perm (Fin 3) => parity (toTable σ))
      (fun σ τ => by
        rw [smul_eq_smul_iff, hfix, map_mul, map_inv, inv_mul_eq_one,
          parity_toTable, parity_toTable]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;>
          rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2 <;>
          simp [h1, h2])
    refine ⟨2, Or.inr (Or.inl rfl), hc, lab, ?_, hinj, ?_⟩
    · rintro x ⟨σ, rfl⟩
      show lab (σ • a) < 2
      rw [hlab, parity_toTable]
      split <;> omega
    · rintro ρ x ⟨σ, rfl⟩
      show lab (ρ • σ • a) = stdAct 2 (toTable ρ) (lab (σ • a))
      rw [← mul_smul, hlab, hlab, toTable_mul,
        parity_compose _ (toTable_mem ρ) _ (toTable_mem σ)]
      exact Nat.xor_comm _ _
  · -- size 3: the natural action
    obtain ⟨lab, hlab, hinj⟩ := exists_orbit_labeling a
      (fun σ : Equiv.Perm (Fin 3) => (σ k).val)
      (fun σ τ => by
        rw [smul_eq_smul_iff, hfix, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq,
          Fin.val_inj])
    refine ⟨3, Or.inr (Or.inr (Or.inl rfl)), hc, lab, ?_, hinj, ?_⟩
    · rintro x ⟨σ, rfl⟩
      show lab (σ • a) < 3
      rw [hlab]
      exact (σ k).isLt
    · rintro ρ x ⟨σ, rfl⟩
      show lab (ρ • σ • a) = stdAct 3 (toTable ρ) (lab (σ • a))
      rw [← mul_smul, hlab, hlab]
      exact (app_toTable ρ (σ k)).symm
  · -- size 6: the free orbit
    obtain ⟨lab, hlab, hinj⟩ := exists_orbit_labeling a
      (fun σ : Equiv.Perm (Fin 3) => pidx (toTable σ))
      (fun σ τ => by
        rw [smul_eq_smul_iff, hfix, inv_mul_eq_one]
        constructor
        · rintro rfl
          rfl
        · intro h
          exact (toTable_injective (pidx_injective (toTable_mem σ) (toTable_mem τ) h)).symm)
    refine ⟨6, Or.inr (Or.inr (Or.inr rfl)), hc, lab, ?_, hinj, ?_⟩
    · rintro x ⟨σ, rfl⟩
      show lab (σ • a) < 6
      rw [hlab]
      exact pidx_lt _ (toTable_mem σ)
    · rintro ρ x ⟨σ, rfl⟩
      show lab (ρ • σ • a) = stdAct 6 (toTable ρ) (lab (σ • a))
      rw [← mul_smul, hlab, hlab, toTable_mul]
      show _ = pidx (compose (toTable ρ) (perms.getD (pidx (toTable σ)) (0, 1, 2)))
      rw [pidx_getD _ (toTable_mem σ)]

end Def1
