/-!
  Generic list lemmas the proof layers share -- the reusable library
  factored out of the occurrence-level semantics proof (ProofsOcc.lean).
  Everything here is problem-independent: zip-range characterizations,
  countP/any bridges between index space and element space, Nodup
  machinery for filterMap/flatMap, and pairwise strengthening. Core Lean
  only; consumed by the later rounds (the P3 bridge, the P6 multi-clause
  layers). The entries with core drop-ins are one-line wrappers over them
  (`find?_isSome_eq_any`, `pairwise_strengthen`, `countP_congr'`); the
  ones with core or mathlib drop-ins were removed in favour of the library
  (`List.length_filterMap_eq_countP` -- core, [opus5.5 review] --,
  `List.filterMap_eq_flatMap_toList`,
  `List.Sublist.flatMap_right`) at their users. `nodup_eraseDups` lives
  here so that the multi-clause layers need no group-theory import.
-/

namespace Atlas

open List

/-- `eraseDups` produces a duplicate-free list. -/
theorem nodup_eraseDups {β : Type} [BEq β] [LawfulBEq β] :
    ∀ l : List β, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups _⟩
    intro hmem
    rw [List.mem_eraseDups] at hmem
    have hp := (List.mem_filter.mp hmem).2
    simp at hp
termination_by l => l.length
decreasing_by
  have := List.length_filter_le (fun b => !b == a) as
  simp only [List.length_cons]
  omega

theorem zipRange_eq {α : Type} (d : α) (l : List α) :
    (List.range l.length).zip l
      = (List.range l.length).map fun c => (c, l.getD c d) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons,
      List.map_cons, List.getD_cons_zero, List.zip_map_left, ih, List.map_map]
    rfl

theorem mem_zipRange {α : Type} (d : α) {l : List α} {c : Nat} {x : α} :
    (c, x) ∈ (List.range l.length).zip l ↔ c < l.length ∧ x = l.getD c d := by
  rw [zipRange_eq d l]
  constructor
  · intro h
    obtain ⟨c', hc', heq⟩ := List.mem_map.mp h
    injection heq with h1 h2
    subst h1
    exact ⟨List.mem_range.mp hc', h2.symm⟩
  · intro ⟨hc, hx⟩
    exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, by rw [hx]⟩

theorem zipRange_flatMap {α β : Type} (d : α) (f : Nat × α → List β)
    (l : List α) :
    ((List.range l.length).zip l).flatMap f
      = (List.range l.length).flatMap (fun c => f (c, l.getD c d)) := by
  rw [zipRange_eq d, List.flatMap_map]

/-- Core's membership-restricted `List.countP_congr`, with a Boolean
    equality as the hypothesis. -/
theorem countP_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.countP p = l.countP q :=
  fun h => List.countP_congr fun x hx => by rw [h x hx]
theorem any_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.any_cons, List.any_cons, h a (by simp),
      ih fun x hx => h x (mem_cons_of_mem _ hx)]

theorem countP_range_getD {α : Type} (d : α) (q : α → Bool) (l : List α) :
    (List.range l.length).countP (fun c => q (l.getD c d)) = l.countP q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons,
      List.countP_map,
      countP_congr' (p := (fun c => q ((a :: l).getD c d)) ∘ Nat.succ)
        (q := fun c => q (l.getD c d)) (fun _ _ => rfl),
      ih, List.countP_cons]
    rfl

theorem any_range_getD {α : Type} (d : α) (q : α → Bool) (l : List α) :
    (List.range l.length).any (fun c => q (l.getD c d)) = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.any_cons, List.any_map,
      any_congr' (p := (fun c => q ((a :: l).getD c d)) ∘ Nat.succ)
        (q := fun c => q (l.getD c d)) (fun _ _ => rfl),
      ih, List.any_cons]
    rfl

/-- Core's `List.isSome_find?`, in the eta-reduced form the proofs use. -/
theorem find?_isSome_eq_any {α : Type} (p : α → Bool) (l : List α) :
    (l.find? p).isSome = l.any p :=
  List.isSome_find?
theorem zipRange_countP {α : Type} (d : α) (q : α → Bool) (l : List α) :
    ((List.range l.length).zip l).countP (fun p => q p.2) = l.countP q := by
  rw [zipRange_eq d, List.countP_map,
    countP_congr' (p := (fun p => q p.2) ∘ fun c => (c, l.getD c d))
      (q := fun c => q (l.getD c d)) (fun _ _ => rfl)]
  exact countP_range_getD d q l

theorem nodup_filterMap_of_inj {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup →
      (∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') →
      (l.filterMap f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hnd hinj
    rw [List.filterMap_cons]
    have htail := ih (List.nodup_cons.mp hnd).2
      (fun x hx x' hx' b h h' =>
        hinj x (mem_cons_of_mem _ hx) x' (mem_cons_of_mem _ hx') b h h')
    cases hfa : f a with
    | none => exact htail
    | some b =>
      rw [List.nodup_cons]
      refine ⟨?_, htail⟩
      intro hmem
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hmem
      have heq : a = a' :=
        hinj a (by simp) a' (mem_cons_of_mem _ ha') b hfa hfa'
      exact (List.nodup_cons.mp hnd).1 (heq ▸ ha')

/-- Core's `List.Pairwise.imp_of_mem`, in the argument order the proofs
    use. -/
theorem pairwise_strengthen {α : Type} {R S : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R →
      (∀ u ∈ l, ∀ v ∈ l, R u v → S u v) → l.Pairwise S :=
  fun hp h => hp.imp_of_mem fun ha hb r => h _ ha _ hb r
theorem zipRange_nodup {α : Type} (d : α) (l : List α) :
    ((List.range l.length).zip l).Nodup := by
  rw [zipRange_eq d]
  show List.Pairwise _ _
  rw [List.pairwise_map]
  have h : (List.range l.length).Nodup := List.nodup_range
  exact h.imp fun hne hEq => hne (congrArg Prod.fst hEq)

theorem getD_mem_of_lt {α : Type} {l : List α} {i : Nat} (d : α)
    (h : i < l.length) : l.getD i d ∈ l := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ]
      exact mem_cons_of_mem _ (ih (Nat.lt_of_succ_lt_succ h))


end Atlas
