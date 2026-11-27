/-!
  Generic list lemmas shared by the proof layers (core Lean only):
  `nodup_eraseDups` and `any_congr'`.
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

theorem any_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.any_cons, List.any_cons, h a (by simp),
      ih fun x hx => h x (mem_cons_of_mem _ hx)]

end Atlas
