import atlas.Framework
import atlas.Audit
/-!
  Kernel-checked theorems for the composition/arrangement layer -- the
  layer whose silent coverage bug motivated the audit project. The tests
  of atlas-ext2 check these properties at sample points; here the type
  checker closes the bug class outright:

  * `compositions_sound` / `compositions_complete` -- the enumeration
    contains exactly the non-decreasing lists over the legal sizes with
    the right sum: nothing extra, nothing missing, for every k.
  * `compositions_length` -- the enumeration agrees with the independent
    audit count everywhere, not just at the tested points.
  * `arrangeNeg_perm` / `arrangeNeg_head` -- the negative-layer
    arrangement is a permutation that puts a 3 at position 0 (the position
    every current problem declares; the general-position statement carries
    the `p <= length` hypothesis that position 0 satisfies trivially).
  * `slicesFor_eq`, `slicesFor_covers`, `slicesFor_skipped_no3` -- slice
    selection is exactly "arrange the 3-containing compositions, skip the
    rest", so every legal non-decreasing multiset containing a 3 is swept.
    The empirical failure of `slicesFor_covers` was the original bug.

  This file needs no mathlib (its import closure is the framework and the
  audit) and no `sorry`. The search walk (`searchAux`) is total since P3;
  its soundness and completeness live in `atlas/ProofsWalk.lean`.
-/

namespace Atlas

-- ------------------------------------------------------------- legal sizes

theorem legalSizes_pos {sizes : List Nat} : ∀ s ∈ legalSizes sizes, 1 ≤ s := by
  intro s hs
  simp only [legalSizes, List.mem_filter] at hs
  have := hs.1
  simp at this
  omega

theorem legalSizes_sorted {sizes : List Nat} :
    (legalSizes sizes).Pairwise (· < ·) := by
  have h : ([1, 2, 3, 6] : List Nat).Pairwise (· < ·) := by decide
  exact h.sublist List.filter_sublist

-- --------------------------------------------------------------- soundness

theorem compositionsAux_sound :
    ∀ (k : Nat) (ss : List Nat), ∀ c ∈ compositionsAux k ss,
      c.sum = k ∧ ∀ x ∈ c, x ∈ ss := by
  intro k ss
  induction k, ss using compositionsAux.induct with
  | case1 ss =>
    intro c hc
    simp only [compositionsAux, List.mem_singleton] at hc
    simp [hc]
  | case2 n =>
    intro c hc
    simp [compositionsAux] at hc
  | case3 k s rest ih1 ih2 =>
    intro c hc
    by_cases h : 1 ≤ s ∧ s ≤ k + 1
    · simp only [compositionsAux, dif_pos h, List.mem_append, List.mem_map] at hc
      rcases hc with ⟨c', hc', rfl⟩ | hc
      · obtain ⟨hsum, hmem⟩ := ih1 h c' hc'
        constructor
        · simp only [List.sum_cons, hsum]; omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact hmem x hx
      · obtain ⟨hsum, hmem⟩ := ih2 c hc
        exact ⟨hsum, fun x hx => List.mem_cons_of_mem s (hmem x hx)⟩
    · simp only [compositionsAux, dif_neg h, List.nil_append] at hc
      obtain ⟨hsum, hmem⟩ := ih2 c hc
      exact ⟨hsum, fun x hx => List.mem_cons_of_mem s (hmem x hx)⟩

/-- Every element of every enumerated list dominates `a` whenever every
    allowed size does -- the invariant behind sortedness. -/
theorem compositionsAux_ge {a : Nat} (k : Nat) (ss : List Nat)
    (hss : ∀ x ∈ ss, a ≤ x) : ∀ c ∈ compositionsAux k ss, ∀ x ∈ c, a ≤ x :=
  fun c hc x hx => hss x ((compositionsAux_sound k ss c hc).2 x hx)

theorem compositionsAux_pairwise :
    ∀ (k : Nat) (ss : List Nat), ss.Pairwise (· ≤ ·) →
      ∀ c ∈ compositionsAux k ss, c.Pairwise (· ≤ ·) := by
  intro k ss
  induction k, ss using compositionsAux.induct with
  | case1 ss =>
    intro _ c hc
    simp only [compositionsAux, List.mem_singleton] at hc
    simp [hc]
  | case2 n =>
    intro _ c hc
    simp [compositionsAux] at hc
  | case3 k s rest ih1 ih2 =>
    intro hss c hc
    by_cases h : 1 ≤ s ∧ s ≤ k + 1
    · simp only [compositionsAux, dif_pos h, List.mem_append, List.mem_map] at hc
      rcases hc with ⟨c', hc', rfl⟩ | hc
      · refine List.pairwise_cons.mpr ⟨?_, ih1 h hss c' hc'⟩
        refine compositionsAux_ge _ _ ?_ c' hc'
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl x
        · exact (List.pairwise_cons.mp hss).1 x hx
      · exact ih2 (List.pairwise_cons.mp hss).2 c hc
    · simp only [compositionsAux, dif_neg h, List.nil_append] at hc
      exact ih2 (List.pairwise_cons.mp hss).2 c hc

-- ------------------------------------------------------------ completeness

theorem compositionsAux_complete :
    ∀ (k : Nat) (ss : List Nat), ss.Pairwise (· < ·) → (∀ x ∈ ss, 1 ≤ x) →
      ∀ c : List Nat, c.sum = k → (∀ x ∈ c, x ∈ ss) → c.Pairwise (· ≤ ·) →
      c ∈ compositionsAux k ss := by
  intro k ss
  induction k, ss using compositionsAux.induct with
  | case1 ss =>
    intro _ hpos c hsum hmem _
    cases c with
    | nil => simp [compositionsAux]
    | cons x c' =>
      exfalso
      have hx := hpos x (hmem x (List.mem_cons_self ..))
      simp only [List.sum_cons] at hsum
      omega
  | case2 n =>
    intro _ _ c hsum hmem _
    cases c with
    | nil => exact absurd hsum (by simp)
    | cons x c' => exact absurd (hmem x (List.mem_cons_self ..)) (by simp)
  | case3 k s rest ih1 ih2 =>
    intro hss hpos c hsum hmem hchain
    cases c with
    | nil => exact absurd hsum (by simp)
    | cons x c' =>
      have hxss := hmem x (List.mem_cons_self ..)
      have hxpos : 1 ≤ x := hpos x hxss
      have hsum' : x + c'.sum = k + 1 := by simpa [List.sum_cons] using hsum
      rcases List.mem_cons.mp hxss with rfl | hxrest
      · -- the head is the current size: descend into the reuse branch
        have hg : 1 ≤ x ∧ x ≤ k + 1 := ⟨hxpos, by omega⟩
        simp only [compositionsAux, dif_pos hg, List.mem_append]
        refine Or.inl (List.mem_map.mpr ⟨c', ?_, rfl⟩)
        exact ih1 hg hss hpos c' (by omega) (fun y hy => hmem y (List.mem_cons_of_mem x hy))
          (List.pairwise_cons.mp hchain).2
      · -- the head lives further right: the whole list avoids s
        have hsx : s < x := (List.pairwise_cons.mp hss).1 x hxrest
        have hall : ∀ y ∈ x :: c', y ∈ rest := by
          intro y hy
          have hyss := hmem y hy
          have hxy : x ≤ y := by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact Nat.le_refl y
            · exact (List.pairwise_cons.mp hchain).1 y hy'
          rcases List.mem_cons.mp hyss with rfl | hyrest
          · exact absurd hxy (by omega)
          · exact hyrest
        have step := ih2 (List.pairwise_cons.mp hss).2
          (fun y hy => hpos y (List.mem_cons_of_mem s hy)) (x :: c') hsum hall hchain
        by_cases hg : 1 ≤ s ∧ s ≤ k + 1
        · simp only [compositionsAux, dif_pos hg, List.mem_append]
          exact Or.inr step
        · simp only [compositionsAux, dif_neg hg, List.nil_append]
          exact step

-- ------------------------------------------------- the enumeration counted

theorem compositionsAux_length :
    ∀ (k : Nat) (ss : List Nat),
      (compositionsAux k ss).length = countParts k ss := by
  intro k ss
  induction k, ss using compositionsAux.induct with
  | case1 ss => simp [compositionsAux, countParts]
  | case2 n => simp [compositionsAux, countParts]
  | case3 k s rest ih1 ih2 =>
    by_cases h : 1 ≤ s ∧ s ≤ k + 1
    · simp [compositionsAux, countParts, dif_pos h, ih1 h, ih2]
    · simp [compositionsAux, countParts, dif_neg h, ih2]

-- ------------------------------------------------------ the public wrappers

/-- Nothing extra: every enumerated composition is a non-decreasing list
    over the legal sizes with the right sum. -/
theorem compositions_sound {k : Nat} {sizes c : List Nat}
    (h : c ∈ compositions k sizes) :
    c.sum = k ∧ (∀ x ∈ c, x ∈ legalSizes sizes) ∧ c.Pairwise (· ≤ ·) := by
  obtain ⟨hsum, hmem⟩ := compositionsAux_sound k (legalSizes sizes) c h
  exact ⟨hsum, hmem, compositionsAux_pairwise k (legalSizes sizes)
    (legalSizes_sorted.imp Nat.le_of_lt) c h⟩

/-- Nothing missing: every non-decreasing list over the legal sizes with
    the right sum is enumerated -- the theorem that closes the coverage
    bug class for good. -/
theorem compositions_complete {k : Nat} {sizes c : List Nat}
    (hsum : c.sum = k) (hmem : ∀ x ∈ c, x ∈ legalSizes sizes)
    (hchain : c.Pairwise (· ≤ ·)) : c ∈ compositions k sizes :=
  compositionsAux_complete k (legalSizes sizes) legalSizes_sorted
    legalSizes_pos c hsum hmem hchain

/-- The enumeration agrees with the independent audit count everywhere. -/
theorem compositions_length (k : Nat) (sizes : List Nat) :
    (compositions k sizes).length = partitionCount k sizes :=
  compositionsAux_length k (legalSizes sizes)

-- ------------------------------------------------------- the arrangement

/-- Arranging is a permutation: nothing is lost or invented when the 3 is
    moved to the declared position. -/
theorem arrangeNeg_perm {c : List Nat} (h : (3 : Nat) ∈ c) {p : Nat}
    (hp : p ≤ (c.erase 3).length) : (arrangeNeg c p).Perm c := by
  unfold arrangeNeg
  exact (List.perm_insertIdx 3 (c.erase 3) hp).trans (List.perm_cons_erase h).symm

/-- At position 0 -- the position every current problem declares -- the
    arranged slice starts with the size-3 part. -/
theorem arrangeNeg_head (c : List Nat) : (arrangeNeg c 0).getD 0 0 = 3 := by
  simp [arrangeNeg]

-- ----------------------------------------------------- the slice selection

/-- Slice selection, characterized: run exactly the 3-containing
    compositions (arranged), skip exactly the rest. -/
theorem slicesFor_eq (p k : Nat) (sizes : List Nat) :
    slicesFor (some p) k sizes true false
      = (((compositions k sizes).filter (fun c => c.contains 3)).map
           (arrangeNeg · p),
         (compositions k sizes).filter (fun c => !c.contains 3)) := by
  simp [slicesFor, List.partition_eq_filter_filter]

/-- Skipped compositions really are 3-free. -/
theorem slicesFor_skipped_no3 {p k : Nat} {sizes c : List Nat}
    (h : c ∈ (slicesFor (some p) k sizes true false).2) : (3 : Nat) ∉ c := by
  rw [slicesFor_eq] at h
  simpa using (List.mem_filter.mp h).2

/-- Every run slice is a permutation of a 3-containing composition. -/
theorem slicesFor_run_perm {k : Nat} {sizes c : List Nat}
    (h : c ∈ (slicesFor (some 0) k sizes true false).1) :
    ∃ c₀ ∈ compositions k sizes, c.Perm c₀ ∧ (3 : Nat) ∈ c₀ := by
  rw [slicesFor_eq] at h
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp h
  have h3 : (3 : Nat) ∈ c₀ := by simpa using (List.mem_filter.mp hc₀).2
  exact ⟨c₀, (List.mem_filter.mp hc₀).1, arrangeNeg_perm h3 (Nat.zero_le _), h3⟩

/-- The coverage theorem, end to end: every legal non-decreasing multiset
    that contains a 3 is arranged into the run list of the sweep. The
    empirical failure of exactly this statement was the original bug. -/
theorem slicesFor_covers {k : Nat} {sizes c : List Nat}
    (hsum : c.sum = k) (hmem : ∀ x ∈ c, x ∈ legalSizes sizes)
    (hchain : c.Pairwise (· ≤ ·)) (h3 : (3 : Nat) ∈ c) :
    arrangeNeg c 0 ∈ (slicesFor (some 0) k sizes true false).1 := by
  rw [slicesFor_eq]
  refine List.mem_map.mpr ⟨c, List.mem_filter.mpr
    ⟨compositions_complete hsum hmem hchain, ?_⟩, rfl⟩
  simpa using h3

end Atlas
