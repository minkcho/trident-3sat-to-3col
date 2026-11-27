/-!
  A generic list lemma shared by the proof layers (core Lean only):
  `any_congr'`.
-/

namespace Atlas

open List

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
