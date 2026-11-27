import atlas.Framework
/-!
  Kernel-checked theorems for the composition layer:
  `compositions_sound` / `compositions_complete` -- the enumeration contains
  exactly the non-decreasing lists over the legal sizes with the right sum,
  for every k (nothing extra, nothing missing). Statement 5 of
  `Statement.lean` restates them for the sizes [1, 2, 3, 6].
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

end Atlas
