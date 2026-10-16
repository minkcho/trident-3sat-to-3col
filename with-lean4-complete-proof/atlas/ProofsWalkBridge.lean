import Mathlib.Data.List.Forall2
import atlas.ProofsWalk
import atlas.ProofsKits
/-!
  The bridge from the walk's own enumeration to the universe's: the leaf
  graph of mask m is a permutation of `graphAt base free m`, the
  3-coloring verifier is invariant under edge permutation, and therefore
  the P3 exhaustiveness theorem transfers to `Universe.graphs`/`gadgetK`
  form: an empty found list means `gadgetK` rejects EVERY graph of the
  slice.
-/

namespace Atlas

open List

-- ------------------------------------------------- permutation utilities

theorem all_congr' {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.all p = l.all q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.all_cons, List.all_cons, h a (by simp),
      ih fun x hx => h x (mem_cons_of_mem _ hx)]

/-- Mathlib's membership-restricted `List.flatMap_congr`, under the name
    the proofs use. -/
theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g :=
  fun h => List.flatMap_congr h
-- --------------------------------------- walk graphs are universe graphs

/-- The selector inside `graphAt` is the flattened bit subset. -/
theorem graphAt_selector :
    ∀ (free : List (List Edge)) (mask : Nat),
      (((List.range free.length).zip free).flatMap fun p =>
        if mask >>> p.1 &&& 1 == 1 then p.2 else [])
      = (bitSubset mask free).flatten := by
  intro free
  induction free with
  | nil => intro mask; rfl
  | cons g rest ih =>
    intro mask
    rw [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons,
      List.flatMap_cons, List.zip_map_left, List.flatMap_map]
    rw [flatMap_congr' (g := fun p : Nat × List Edge =>
        if (mask >>> 1) >>> p.1 &&& 1 == 1 then p.2 else []) ?_]
    · rw [ih (mask >>> 1)]
      simp only [bitSubset, List.flatten_append, Nat.shiftRight_zero]
      split <;> simp
    · intro p _
      obtain ⟨i, gg⟩ := p
      have hshift : mask >>> (Nat.succ i) = mask >>> 1 >>> i := by
        rw [Nat.succ_eq_add_one, Nat.add_comm, Nat.shiftRight_add]
      simp only [Prod.map, id, hshift]

/-- The walk's leaf graph is a permutation of the flattened bit subset on
    top of the accumulator. -/
theorem walkGraph_perm_flatten :
    ∀ (free : List (List Edge)) (mask : Nat) (acc : List Edge),
      (walkGraph free mask acc).Perm ((bitSubset mask free).flatten ++ acc) := by
  intro free
  induction free with
  | nil =>
    intro mask acc
    simp [walkGraph, bitSubset]
  | cons g rest ih =>
    intro mask acc
    simp only [walkGraph, bitSubset, List.flatten_append]
    by_cases hb : mask &&& 1 == 1
    · rw [if_pos hb, if_pos hb]
      refine (ih (mask >>> 1) (g ++ acc)).trans ?_
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      calc (bitSubset (mask >>> 1) rest).flatten ++ (g ++ acc)
          = ((bitSubset (mask >>> 1) rest).flatten ++ g) ++ acc := by
            rw [List.append_assoc]
        _ ~ (g ++ (bitSubset (mask >>> 1) rest).flatten) ++ acc :=
            (List.perm_append_comm).append_right acc
        _ = g ++ ((bitSubset (mask >>> 1) rest).flatten ++ acc) := by
            rw [List.append_assoc]
        _ = (g ++ (bitSubset (mask >>> 1) rest).flatten) ++ acc := by
            rw [List.append_assoc]
    · rw [if_neg hb, if_neg hb]
      refine (ih (mask >>> 1) acc).trans ?_
      simp

/-- The bridge: the walk's leaf graph and the universe's `graphAt` graph
    are the same edge set. -/
theorem walkGraph_perm_graphAt (base : List Edge) (free : List (List Edge))
    (mask : Nat) :
    (walkGraph free mask base).Perm (graphAt base free mask) := by
  unfold graphAt
  rw [graphAt_selector free mask]
  exact (walkGraph_perm_flatten free mask base).trans List.perm_append_comm

-- ------------- the 3-coloring verifier is invariant under edge-list permutation
-- [opus5.5 review] header was "set-level"; the lemmas below are about `Perm`

theorem colorableGo_perm {α : Type} [BEq α] {edges₁ edges₂ : List (α × α)}
    (h : edges₁.Perm edges₂) (pins : List (α × Nat)) :
    ∀ (rest : List α) (assign : List (α × Nat)),
      colorableGo edges₁ pins rest assign = colorableGo edges₂ pins rest assign := by
  intro rest
  induction rest with
  | nil => intro _; rfl
  | cons v rest ih =>
    intro assign
    simp only [colorableGo]
    refine any_congr' ?_
    intro c _
    have hadj : (adjTo edges₁ v).any
        (fun u => ((assign.find? (·.1 == u)).map (·.2)) == some c)
      = (adjTo edges₂ v).any
        (fun u => ((assign.find? (·.1 == u)).map (·.2)) == some c) :=
      (h.filterMap _).any_eq
    rw [hadj]
    by_cases hconf : (adjTo edges₂ v).any
        (fun u => ((assign.find? (·.1 == u)).map (·.2)) == some c) = true
    · rw [if_pos hconf, if_pos hconf]
    · rw [if_neg hconf, if_neg hconf]
      exact ih ((v, c) :: assign)

theorem colorsOk_perm {α : Type} [BEq α] {i i' : Instance α}
    (hv : i.verts = i'.verts) (ha : i.anchors = i'.anchors)
    (hs : i.selected = i'.selected) (hf : i.forbidden = i'.forbidden)
    (he : i.edges.Perm i'.edges) : colorsOk i = colorsOk i' := by
  unfold colorsOk colorable
  rw [hv, ha, hs, hf]
  exact colorableGo_perm he _ _ _

-- `commonK` sees rows only through isSat, measure and exact.
-- [opus5.5 review] the line above was the docstring of the generic lemma
-- below; it becomes a section note and the lemma gets its own docstring

/-- `findSome?` agrees on `Forall₂`-related lists when `f` and `g` agree on
    related elements. -/
theorem findSome?_of_forall₂ {α β γ : Type} {R : α → β → Prop}
    {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      l₁.findSome? f = l₂.findSome? g := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    rw [List.findSome?_cons, List.findSome?_cons, hfg _ _ hr]
    cases g _ with
    | some b => rfl
    | none => exact ih

theorem all_of_forall₂ {α β : Type} {R : α → β → Prop}
    {f : α → Bool} {g : β → Bool}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      l₁.all f = l₂.all g := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    rw [List.all_cons, List.all_cons, hfg _ _ hr, ih]

theorem forall₂_map_map {α β γ : Type} {R : β → γ → Prop}
    {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ a ∈ l, R (f a) (g a)) →
      List.Forall₂ R (l.map f) (l.map g) := by
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons a l ih =>
    intro h
    exact .cons (h a (by simp)) (ih fun x hx => h x (mem_cons_of_mem _ hx))

/-- Extensionality for `commonK`: rows equal in satisfiability flag,
    measure and exact give equal budgets. -/
theorem commonK_ext (P : Problem) {α : Type} [BEq α]
    {rows₁ rows₂ : List (Bool × Instance α)}
    (h : List.Forall₂ (fun r₁ r₂ => r₁.1 = r₂.1 ∧
        P.measure r₁.2 = P.measure r₂.2 ∧
        ∀ k, P.exact r₁.2 k = P.exact r₂.2 k) rows₁ rows₂) :
    commonK P rows₁ = commonK P rows₂ := by
  unfold commonK
  have hstep : ∀ (x y : Option Nat) (f g : Nat → Option Nat),
      x = y → (∀ k, f k = g k) → (x >>= f) = (y >>= g) := by
    intro x y f g hxy hfg
    rw [hxy]
    cases y with
    | none => rfl
    | some k => exact hfg k
  apply hstep
  · refine findSome?_of_forall₂ ?_ h
    intro a b hab
    obtain ⟨h1, h2, _⟩ := hab
    obtain ⟨s₁, i₁⟩ := a
    obtain ⟨s₂, i₂⟩ := b
    dsimp only at h1 h2 ⊢
    rw [h1, h2]
  · intro k
    have hite : ∀ (b₁ b₂ : Bool) (x y : Option Nat), b₁ = b₂ →
        (if b₁ then x else y) = (if b₂ then x else y) := by
      intro b₁ b₂ x y hb
      rw [hb]
    apply hite
    refine all_of_forall₂ ?_ h
    intro a b hab
    obtain ⟨h1, h2, h3⟩ := hab
    obtain ⟨s₁, i₁⟩ := a
    obtain ⟨s₂, i₂⟩ := b
    dsimp only at h1 h2 h3 ⊢
    rw [h1, h2, h3 k]

/-- `checkGadget` for 3-coloring is invariant under permutation of the
    edge list ([opus5.5 review] was "only through its edge set"; the
    set-level form is `checkGadget_congr_3col`, ProofsCover). -/
theorem checkGadget_perm_3col (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex)) {g g' : List Edge}
    (h : g.Perm g') :
    checkGadget threeColoring U anchors rows g
      = checkGadget threeColoring U anchors rows g' := by
  unfold checkGadget
  apply commonK_ext
  refine forall₂_map_map ?_
  intro r _
  obtain ⟨isSat, sel, forb⟩ := r
  dsimp only
  have hco : colorsOk { verts := U.vertices, edges := g, anchors := anchors, selected := sel, forbidden := forb }
      = colorsOk { verts := U.vertices, edges := g', anchors := anchors, selected := sel, forbidden := forb } :=
    colorsOk_perm rfl rfl rfl rfl h
  refine ⟨rfl, ?_, ?_⟩
  · simp only [threeColoring, feasibility, hco]
  · intro k
    simp only [threeColoring, feasibility, hco]

-- ------------------------------------------- the gadgetK-form headline

/-- `gadgetK` for 3-coloring is its `checkGadget` (the negative-layer gate
    is trivially open). -/
theorem gadgetK_3col_eq (parts : List Nat) (symmetry : Bool) (g : List Edge) :
    gadgetK threeColoring parts g symmetry
      = checkGadget threeColoring (threeColoring.attach parts).1
          (anchorsOf parts.length (threeColoring.attach parts).1)
          (gadgetRows threeColoring symmetry) g := by
  unfold gadgetK
  rcases hUf : threeColoring.attach parts with ⟨U, forced⟩
  have hneg : negLayerOk threeColoring U = true := rfl
  simp [hneg]

/-- P3, universe form: an empty found list on the 3-coloring slice means
    `gadgetK` rejects every graph of the slice. The paper's negative
    claims are this theorem plus one run of the sweep. -/
theorem searchSlice_exhaustive_threeColoring_graphs (parts : List Nat)
    (symmetry : Bool)
    (h : (searchSlice threeColoring parts symmetry).2.found = []) :
    ∀ g ∈ (threeColoring.attach parts).1.graphs (symmetry := symmetry)
        (forced := (threeColoring.attach parts).2),
      gadgetK threeColoring parts g symmetry = none := by
  intro g hg
  unfold Universe.graphs at hg
  obtain ⟨mask, _, rfl⟩ := List.mem_map.mp hg
  rw [gadgetK_3col_eq]
  cases hchk : checkGadget threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry)
      (graphAt ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 mask) with
  | none => exact hchk
  | some k =>
    exfalso
    have hperm := walkGraph_perm_graphAt
      ((threeColoring.attach parts).1.splitForced
        (threeColoring.attach parts).2 symmetry).1
      ((threeColoring.attach parts).1.splitForced
        (threeColoring.attach parts).2 symmetry).2 mask
    have := checkGadget_perm_3col (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry) hperm
    rw [hchk] at this
    exact searchSlice_exhaustive_threeColoring parts symmetry mask k h this

end Atlas
