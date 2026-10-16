import Mathlib.Data.List.GetD
import atlas.ProofsAction
import atlas.ProofsColor
import atlas.ProofsWalkBridge
/-!
  P4 stage 3: the symmetric verifier equals the raw verifier on
  S3-invariant graphs.

  Route: an order-free characterization of `commonK` (membership only),
  renaming invariance of the 3-coloring verifier along the S3 action
  (via the stage-2 reflection), the induced action on assignment rows,
  and the row-class reduction: for an invariant graph the four-class
  table and the eight-row table produce the same budget
  (`gadgetK_s3_symmetry_reduction`).
-/

namespace Atlas

open List

-- ------------------------------ an order-free reading of the budget logic

/-- The row condition `commonK` tests against a budget k, spelled for a
    single row. -/
def rowCond (P : Problem) {α : Type} [BEq α] (k : Nat)
    (r : Bool × Instance α) : Bool :=
  (match P.measure r.2 with
   | some a => (!r.1 || a == k) && P.target r.1 k a
   | none => false) &&
  (P.exact r.2 k == r.1)

/-- Order- and multiplicity-free characterization of `commonK`: some
    row is satisfiable and every row passes the k test. -/
theorem commonK_eq_some_iff (P : Problem) {α : Type} [BEq α]
    {rows : List (Bool × Instance α)} {k : Nat} :
    commonK P rows = some k ↔
      ((∃ r ∈ rows, r.1 = true) ∧ ∀ r ∈ rows, rowCond P k r = true) := by
  unfold commonK
  constructor
  · intro h
    cases hfs : rows.findSome? fun r => if r.1 then P.measure r.2 else none with
    | none =>
      rw [hfs] at h
      cases h
    | some k₀ =>
      rw [hfs] at h
      have hbind : ∀ f : Nat → Option Nat, (some k₀ >>= f) = f k₀ :=
        fun _ => rfl
      rw [hbind] at h
      dsimp only at h
      split at h
      case isTrue hall =>
        have hk : k₀ = k := Option.some.inj h
        subst hk
        obtain ⟨r₀, hr₀, hf₀⟩ := List.exists_of_findSome?_eq_some hfs
        constructor
        · refine ⟨r₀, hr₀, ?_⟩
          by_cases hsat : r₀.1
          · exact hsat
          · rw [if_neg hsat] at hf₀
            cases hf₀
        · intro r hr
          have := List.all_eq_true.mp hall r hr
          obtain ⟨risSat, rinst⟩ := r
          exact this
      case isFalse => cases h
  · intro ⟨⟨r₀, hr₀, hsat⟩, hall⟩
    have hms : (P.measure r₀.2).isSome = true := by
      have := hall r₀ hr₀
      unfold rowCond at this
      simp only [Bool.and_eq_true] at this
      obtain ⟨hm, _⟩ := this
      cases hmm : P.measure r₀.2 with
      | some a => rfl
      | none =>
        rw [hmm] at hm
        cases hm
    have hsome : (rows.findSome? fun r =>
        if r.1 then P.measure r.2 else none).isSome = true := by
      refine List.findSome?_isSome_iff.mpr ⟨_, hr₀, ?_⟩
      rw [hsat, if_pos rfl]
      exact hms
    cases hfs : rows.findSome? fun r => if r.1 then P.measure r.2 else none with
    | none =>
      rw [hfs] at hsome
      cases hsome
    | some k₀ =>
      have hk₀ : k₀ = k := by
        obtain ⟨r₁, hr₁, hf₁⟩ := List.exists_of_findSome?_eq_some hfs
        have hc := hall r₁ hr₁
        unfold rowCond at hc
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hm, _⟩ := hc
        by_cases hsat₁ : r₁.1
        · rw [if_pos hsat₁] at hf₁
          rw [hf₁] at hm
          simp only [Bool.and_eq_true] at hm
          obtain ⟨hka, _⟩ := hm
          rw [hsat₁] at hka
          simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hka
          exact hka
        · rw [if_neg hsat₁] at hf₁
          cases hf₁
      subst hk₀
      have hbind : ∀ f : Nat → Option Nat, (some k₀ >>= f) = f k₀ :=
        fun _ => rfl
      rw [hbind]
      dsimp only
      rw [if_pos ?_]
      refine List.all_eq_true.mpr ?_
      intro r hr
      have := hall r hr
      obtain ⟨risSat, rinst⟩ := r
      exact this

/-- `commonK` is a congruence for row correspondence: when every row of
    each list has a counterpart in the other with the same satisfiability
    flag, the same measure and the same faithful column, both lists read
    the same budget (order and multiplicity are irrelevant, by
    `commonK_eq_some_iff`). -/
theorem commonK_eq_of_quotient (P : Problem) {α : Type} [BEq α]
    {rows₁ rows₂ : List (Bool × Instance α)}
    (h12 : ∀ r ∈ rows₁, ∃ r' ∈ rows₂, r.1 = r'.1 ∧
      P.measure r.2 = P.measure r'.2 ∧ ∀ k, P.exact r.2 k = P.exact r'.2 k)
    (h21 : ∀ r' ∈ rows₂, ∃ r ∈ rows₁, r'.1 = r.1 ∧
      P.measure r'.2 = P.measure r.2 ∧ ∀ k, P.exact r'.2 k = P.exact r.2 k) :
    commonK P rows₁ = commonK P rows₂ := by
  have key : ∀ k, commonK P rows₁ = some k ↔ commonK P rows₂ = some k := by
    intro k
    rw [commonK_eq_some_iff, commonK_eq_some_iff]
    constructor
    · intro ⟨⟨r, hr, hsat⟩, hall⟩
      obtain ⟨r', hr', h1, _, _⟩ := h12 r hr
      refine ⟨⟨r', hr', h1 ▸ hsat⟩, ?_⟩
      intro q hq
      obtain ⟨p, hp, e1, e2, e3⟩ := h21 q hq
      have := hall p hp
      unfold rowCond at this ⊢
      rw [e1, e2, e3 k]
      exact this
    · intro ⟨⟨r', hr', hsat⟩, hall⟩
      obtain ⟨r, hr, h1, _, _⟩ := h21 r' hr'
      refine ⟨⟨r, hr, h1 ▸ hsat⟩, ?_⟩
      intro q hq
      obtain ⟨p, hp, e1, e2, e3⟩ := h12 q hq
      have := hall p hp
      unfold rowCond at this ⊢
      rw [e1, e2, e3 k]
      exact this
  cases h1 : commonK P rows₁ with
  | some k => exact ((key k).mp h1).symm
  | none =>
    cases h2 : commonK P rows₂ with
    | some k =>
      have := (key k).mpr h2
      rw [h1] at this
      cases this
    | none => rfl

-- ------------------------- the induced action on assignments (finite core)

/-- The bit-permutation action on an assignment: bit `app s i` of the
    image is bit `i` of the argument. -/
def envAct (s : Perm) (env : Nat) : Nat :=
  ((env >>> 0 &&& 1) <<< app s 0) ||| ((env >>> 1 &&& 1) <<< app s 1) |||
    ((env >>> 2 &&& 1) <<< app s 2)

theorem envAct_bit : ∀ s ∈ perms, ∀ env, env < 8 → ∀ i, i < 3 →
    (envAct s env >>> app s i &&& 1) = (env >>> i &&& 1) := by decide

theorem envAct_ne_zero : ∀ s ∈ perms, ∀ env, env < 8 →
    ((envAct s env != 0) = (env != 0)) := by decide

theorem app_surj : ∀ s ∈ perms, ∀ j, j < 3 →
    ∃ i ∈ List.range 3, app s i = j := by decide

/-- Every assignment is the image of a class representative: the four
    classes [0, 1, 3, 7] cover the eight rows under the bit action. -/
theorem exists_class_rep : ∀ env, env < 8 →
    ∃ rep ∈ [0, 1, 3, 7], ∃ s ∈ perms, envAct s rep = env := by decide

theorem reps_mem_range : ∀ env ∈ [0, 1, 3, 7], env ∈ List.range 8 := by decide

theorem reps_lt : ∀ rep ∈ [0, 1, 3, 7], rep < 8 := by decide

-- ------------------------------------ the 3-coloring attach, concretely

theorem attach_parts (parts : List Nat) :
    (threeColoring.attach parts).1.parts = parts ++ [1, 1, 1] := rfl

theorem attach_anchors (parts : List Nat) :
    anchorsOf parts.length (threeColoring.attach parts).1
      = [.aux parts.length 0, .aux (parts.length + 1) 0,
         .aux (parts.length + 2) 0] := by
  unfold anchorsOf
  have h3 : (threeColoring.attach parts).1.parts.length - parts.length = 3 := by
    rw [attach_parts, List.length_append]
    simp
  rw [h3]
  rfl

theorem attach_size (parts : List Nat) {d : Nat} (hd : d < 3) :
    (threeColoring.attach parts).1.size (parts.length + d) = 1 := by
  show (parts ++ [1, 1, 1]).getD (parts.length + d) 0 = 1
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]
  interval_cases d <;> rfl

theorem attach_legal (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) :
    (threeColoring.attach parts).1.legal := by
  intro n hn
  rw [attach_parts] at hn
  rcases List.mem_append.mp hn with h | h
  · exact hparts n h
  · left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> rfl

-- --------------------------------------------- colorAt under renaming

variable {α : Type} [BEq α] [LawfulBEq α]

theorem beq_map {β : Type} [BEq β] [LawfulBEq β] {S : List α} {σ : α → β}
    {σ' : β → α} (hlr : ∀ v ∈ S, σ' (σ v) = v)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) : (σ a == σ b) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · have hσ : ¬σ a = σ b := fun hab => h (by rw [← hlr a ha, hab, hlr b hb])
    cases hab : (σ a == σ b) with
    | true => exact absurd (eq_of_beq hab) hσ
    | false =>
      cases hab' : (a == b) with
      | true => exact absurd (eq_of_beq hab') h
      | false => rfl

theorem colorAt_map {β : Type} [BEq β] [LawfulBEq β] {S : List α}
    {σ : α → β} {σ' : β → α} (hlr : ∀ v ∈ S, σ' (σ v) = v)
    {pins : List (α × Nat)} (hpins : ∀ p ∈ pins, p.1 ∈ S) {v : α}
    (hv : v ∈ S) :
    colorAt (pins.map fun p => (σ p.1, p.2)) (σ v) = colorAt pins v := by
  induction pins with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w, c⟩ := p
    rw [List.map_cons, colorAt_cons, colorAt_cons,
      beq_map hlr (hpins (w, c) (List.mem_cons_self ..)) hv]
    by_cases h : (w == v) = true
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact ih fun q hq => hpins q (List.mem_cons_of_mem _ hq)

theorem mem_of_colorAt_eq_some {pins : List (α × Nat)} {u : α} {c : Nat}
    (h : colorAt pins u = some c) : (u, c) ∈ pins := by
  unfold colorAt at h
  cases hf : pins.find? (·.1 == u) with
  | none =>
    rw [hf] at h
    cases h
  | some p =>
    rw [hf] at h
    have hp : p ∈ pins := List.mem_of_find?_eq_some hf
    have hkey := List.find?_some hf
    have hc : p.2 = c := Option.some.inj h
    rw [← eq_of_beq hkey, ← hc]
    exact hp

theorem colorAt_eq_some_of_mem {pins : List (α × Nat)} {u : α} {c : Nat}
    (hnd : (pins.map (·.1)).Nodup) (hm : (u, c) ∈ pins) :
    colorAt pins u = some c := by
  induction pins with
  | nil => cases hm
  | cons p rest ih =>
    obtain ⟨w, d⟩ := p
    rw [List.map_cons] at hnd
    obtain ⟨hw, hnd'⟩ := List.nodup_cons.mp hnd
    rw [colorAt_cons]
    rcases List.mem_cons.mp hm with heq | hm'
    · have h1 : u = w := congrArg Prod.fst heq
      have h2 : c = d := congrArg Prod.snd heq
      subst h1; subst h2
      rw [if_pos (by simp)]
    · by_cases hbe : (w == u) = true
      · exfalso
        have : u ∈ rest.map (·.1) := List.mem_map.mpr ⟨(u, c), hm', rfl⟩
        rw [eq_of_beq hbe] at hw
        exact hw this
      · rw [if_neg hbe]
        exact ih hnd' hm'

theorem colorAt_congr_mem {pins₁ pins₂ : List (α × Nat)}
    (h1 : (pins₁.map (·.1)).Nodup) (h2 : (pins₂.map (·.1)).Nodup)
    (h : ∀ p : α × Nat, p ∈ pins₁ ↔ p ∈ pins₂) (u : α) :
    colorAt pins₁ u = colorAt pins₂ u := by
  cases hc : colorAt pins₁ u with
  | some c =>
    exact (colorAt_eq_some_of_mem h2 ((h _).mp (mem_of_colorAt_eq_some hc))).symm
  | none =>
    cases hc2 : colorAt pins₂ u with
    | none => rfl
    | some c =>
      have := colorAt_eq_some_of_mem h1 ((h _).mpr (mem_of_colorAt_eq_some hc2))
      rw [hc] at this
      cases this

-- ------------------------------------------ the spec sees edges as a set

theorem adjTo_congr_mem {edges₁ edges₂ : List (α × α)}
    (h : ∀ e : α × α, e ∈ edges₁ ↔ e ∈ edges₂) (v u : α) :
    u ∈ adjTo edges₁ v ↔ u ∈ adjTo edges₂ v := by
  rw [mem_adjTo, mem_adjTo, h (v, u), h (u, v)]

theorem SpecExt_congr_edges {edges₁ edges₂ : List (α × α)}
    {pins : List (α × Nat)} {verts : List α}
    (h : ∀ v u : α, u ∈ adjTo edges₁ v ↔ u ∈ adjTo edges₂ v)
    {f : α → Nat} (hs : SpecExt edges₁ pins verts [] f) :
    SpecExt edges₂ pins verts [] f := by
  obtain ⟨hpin, hconf⟩ := hs
  exact ⟨hpin, fun v hv u hu => hconf v hv u ((h v u).mpr hu)⟩

theorem colorable_congr_edges {edges₁ edges₂ : List (α × α)} (verts : List α)
    (pins : List (α × Nat)) (hloop₁ : ∀ a : α, a ∉ adjTo edges₁ a)
    (hnd : verts.Nodup)
    (h : ∀ v u : α, u ∈ adjTo edges₁ v ↔ u ∈ adjTo edges₂ v) :
    colorable edges₁ verts pins = colorable edges₂ verts pins := by
  have hloop₂ : ∀ a : α, a ∉ adjTo edges₂ a := fun a ha =>
    hloop₁ a ((h a a).mpr ha)
  have h1 := colorable_iff_spec edges₁ verts pins hloop₁ hnd
  have h2 := colorable_iff_spec edges₂ verts pins hloop₂ hnd
  cases hc : colorable edges₂ verts pins
  · cases hc1 : colorable edges₁ verts pins
    · rfl
    · obtain ⟨f, hf⟩ := h1.mp hc1
      have := h2.mpr ⟨f, SpecExt_congr_edges h hf⟩
      rw [hc] at this
      cases this
  · obtain ⟨f, hf⟩ := h2.mp hc
    exact h1.mpr ⟨f, SpecExt_congr_edges (fun v u => (h v u).symm) hf⟩

-- --------------------------------------- normalization is adjacency-free

theorem mem_of_normEdge_mem {g : List Edge} {a b : Vertex}
    (h : (a, b) ∈ g.map normEdge) : (a, b) ∈ g ∨ (b, a) ∈ g := by
  obtain ⟨e, he, heq⟩ := List.mem_map.mp h
  unfold normEdge at heq
  split at heq
  · exact Or.inl (heq ▸ he)
  · have h1 : e.2 = a := congrArg Prod.fst heq
    have h2 : e.1 = b := congrArg Prod.snd heq
    rw [← h1, ← h2]
    exact Or.inr he

theorem adjTo_map_normEdge (g : List Edge) (v u : Vertex) :
    u ∈ adjTo (g.map normEdge) v ↔ u ∈ adjTo g v := by
  rw [mem_adjTo, mem_adjTo]
  constructor
  · rintro (h | h)
    · rcases mem_of_normEdge_mem h with h' | h'
      exacts [Or.inl h', Or.inr h']
    · rcases mem_of_normEdge_mem h with h' | h'
      exacts [Or.inr h', Or.inl h']
  · have push : ∀ a b : Vertex, (a, b) ∈ g →
        ((a, b) ∈ g.map normEdge ∨ (b, a) ∈ g.map normEdge) := by
      intro a b hab
      have hm : normEdge (a, b) ∈ g.map normEdge :=
        List.mem_map.mpr ⟨(a, b), hab, rfl⟩
      unfold normEdge at hm
      split at hm
      · exact Or.inl hm
      · exact Or.inr hm
    rintro (h | h)
    · rcases push v u h with h' | h'
      exacts [Or.inl h', Or.inr h']
    · rcases push u v h with h' | h'
      exacts [Or.inr h', Or.inl h']

-- ---------------------------------------------------- renaming invariance

theorem adjTo_map_of {β : Type} [BEq β] [LawfulBEq β] {σ : α → β}
    {edges : List (α × α)} {w x : α} (hx : x ∈ adjTo edges w) :
    σ x ∈ adjTo (edges.map fun e => (σ e.1, σ e.2)) (σ w) := by
  rcases mem_adjTo.mp hx with h | h
  · exact mem_adjTo.mpr (Or.inl (List.mem_map.mpr ⟨(w, x), h, rfl⟩))
  · exact mem_adjTo.mpr (Or.inr (List.mem_map.mpr ⟨(x, w), h, rfl⟩))

theorem adjTo_map_decomp {β : Type} [BEq β] [LawfulBEq β] {S : List α}
    {σ : α → β} {σ' : β → α}
    (hlr : ∀ v ∈ S, σ' (σ v) = v) {edges : List (α × α)}
    (hedges : ∀ e ∈ edges, e.1 ∈ S ∧ e.2 ∈ S) {w : α} (hw : w ∈ S) {u : β}
    (hu : u ∈ adjTo (edges.map fun e => (σ e.1, σ e.2)) (σ w)) :
    ∃ x, x ∈ S ∧ x ∈ adjTo edges w ∧ u = σ x := by
  rcases mem_adjTo.mp hu with hmem | hmem
  · obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    have h1 : σ e.1 = σ w := congrArg Prod.fst heq
    have h2 : σ e.2 = u := congrArg Prod.snd heq
    have he1 : e.1 = w := by
      rw [← hlr e.1 (hedges e he).1, h1, hlr w hw]
    refine ⟨e.2, (hedges e he).2, ?_, h2.symm⟩
    exact mem_adjTo.mpr (Or.inl (he1 ▸ (show (e.1, e.2) ∈ edges from he)))
  · obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    have h1 : σ e.1 = u := congrArg Prod.fst heq
    have h2 : σ e.2 = σ w := congrArg Prod.snd heq
    have he2 : e.2 = w := by
      rw [← hlr e.2 (hedges e he).2, h2, hlr w hw]
    refine ⟨e.1, (hedges e he).1, ?_, h1.symm⟩
    exact mem_adjTo.mpr (Or.inr (he2 ▸ (show (e.1, e.2) ∈ edges from he)))

theorem SpecExt_rename_fwd {β : Type} [BEq β] [LawfulBEq β] {S : List α}
    {σ : α → β} {σ' : β → α}
    (hlr : ∀ v ∈ S, σ' (σ v) = v) {edges : List (α × α)}
    {pins : List (α × Nat)} {verts : List α}
    (hedges : ∀ e ∈ edges, e.1 ∈ S ∧ e.2 ∈ S) (hverts : ∀ v ∈ verts, v ∈ S)
    (hpins : ∀ p ∈ pins, p.1 ∈ S) {f : α → Nat}
    (hs : SpecExt edges pins verts [] f) :
    SpecExt (edges.map fun e => (σ e.1, σ e.2))
      (pins.map fun p => (σ p.1, p.2)) (verts.map σ) []
      (fun u => f (σ' u)) := by
  obtain ⟨hpin, hconf⟩ := hs
  constructor
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hpw := hpin w hw
    unfold pinOk at hpw ⊢
    rw [colorAt_map hlr hpins (hverts w hw)]
    simp only [hlr w (hverts w hw)]
    exact hpw
  · intro v hv u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨x, hxS, hxadj, rfl⟩ :=
      adjTo_map_decomp hlr hedges (hverts w hw) hu
    unfold combined
    by_cases hxm : σ x ∈ verts.map σ
    · rw [if_pos hxm]
      obtain ⟨x', hx', hxx⟩ := List.mem_map.mp hxm
      have hx'x : x' = x := by
        rw [← hlr x' (hverts x' hx'), hxx, hlr x hxS]
      have hxv : x ∈ verts := hx'x ▸ hx'
      have hcf := hconf w hw x hxadj
      unfold combined at hcf
      rw [if_pos hxv] at hcf
      simp only [hlr x hxS, hlr w (hverts w hw)]
      exact hcf
    · rw [if_neg hxm, colorAt_nil]
      exact fun h => nomatch h

theorem SpecExt_rename_bwd {β : Type} [BEq β] [LawfulBEq β] {S : List α}
    {σ : α → β} {σ' : β → α}
    (hlr : ∀ v ∈ S, σ' (σ v) = v) {edges : List (α × α)}
    {pins : List (α × Nat)} {verts : List α}
    (hverts : ∀ v ∈ verts, v ∈ S)
    (hpins : ∀ p ∈ pins, p.1 ∈ S) {f₂ : β → Nat}
    (hs : SpecExt (edges.map fun e => (σ e.1, σ e.2))
      (pins.map fun p => (σ p.1, p.2)) (verts.map σ) [] f₂) :
    SpecExt edges pins verts [] (fun v => f₂ (σ v)) := by
  obtain ⟨hpin, hconf⟩ := hs
  constructor
  · intro v hv
    have hpv := hpin (σ v) (List.mem_map.mpr ⟨v, hv, rfl⟩)
    unfold pinOk at hpv ⊢
    rw [colorAt_map hlr hpins (hverts v hv)] at hpv
    exact hpv
  · intro v hv u hu
    have hcf := hconf (σ v) (List.mem_map.mpr ⟨v, hv, rfl⟩) (σ u)
      (adjTo_map_of hu)
    unfold combined at hcf ⊢
    by_cases hum : u ∈ verts
    · rw [if_pos hum]
      rw [if_pos (List.mem_map.mpr ⟨u, hum, rfl⟩)] at hcf
      exact hcf
    · rw [if_neg hum, colorAt_nil]
      exact fun h => nomatch h

/-- Renaming invariance: pushing a map that is left-invertible on a
    carrier through an instance whose data lives on the carrier does not
    change the verifier's answer. -/
theorem colorable_rename {β : Type} [BEq β] [LawfulBEq β] {S : List α}
    {σ : α → β} {σ' : β → α}
    (hlr : ∀ v ∈ S, σ' (σ v) = v) (edges : List (α × α)) (verts : List α)
    (pins : List (α × Nat)) (hedges : ∀ e ∈ edges, e.1 ∈ S ∧ e.2 ∈ S)
    (hne : ∀ e ∈ edges, e.1 ≠ e.2) (hverts : ∀ v ∈ verts, v ∈ S)
    (hpins : ∀ p ∈ pins, p.1 ∈ S) (hnd : verts.Nodup) :
    colorable (edges.map fun e => (σ e.1, σ e.2)) (verts.map σ)
        (pins.map fun p => (σ p.1, p.2))
      = colorable edges verts pins := by
  have hloop₁ : ∀ a : α, a ∉ adjTo edges a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h
    · exact hne (a, a) h rfl
    · exact hne (a, a) h rfl
  have hloop₂ : ∀ a : β, a ∉ adjTo (edges.map fun e => (σ e.1, σ e.2)) a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h
    · obtain ⟨e, he, heq⟩ := List.mem_map.mp h
      have h1 : σ e.1 = a := congrArg Prod.fst heq
      have h2 : σ e.2 = a := congrArg Prod.snd heq
      exact hne e he (by
        rw [← hlr e.1 (hedges e he).1, ← hlr e.2 (hedges e he).2, h1, h2])
    · obtain ⟨e, he, heq⟩ := List.mem_map.mp h
      have h1 : σ e.1 = a := congrArg Prod.fst heq
      have h2 : σ e.2 = a := congrArg Prod.snd heq
      exact hne e he (by
        rw [← hlr e.1 (hedges e he).1, ← hlr e.2 (hedges e he).2, h1, h2])
  have hnd₂ : (verts.map σ).Nodup :=
    hnd.map_on fun x hx y hy hxy => by
      rw [← hlr x (hverts x hx), hxy, hlr y (hverts y hy)]
  have h1 := colorable_iff_spec edges verts pins hloop₁ hnd
  have h2 := colorable_iff_spec (edges.map fun e => (σ e.1, σ e.2))
    (verts.map σ) (pins.map fun p => (σ p.1, p.2)) hloop₂ hnd₂
  cases hc : colorable edges verts pins
  · cases hc2 : colorable (edges.map fun e => (σ e.1, σ e.2)) (verts.map σ)
        (pins.map fun p => (σ p.1, p.2))
    · rfl
    · obtain ⟨f₂, hf₂⟩ := h2.mp hc2
      have := h1.mpr ⟨fun v => f₂ (σ v),
        SpecExt_rename_bwd hlr hverts hpins hf₂⟩
      rw [hc] at this
      cases this
  · obtain ⟨f, hf⟩ := h1.mp hc
    exact h2.mpr ⟨fun u => f (σ' u),
      SpecExt_rename_fwd hlr hedges hverts hpins hf⟩

-- ------------------------------------ the gadget rows, membership-level

theorem mem_selected {env : Nat} {v : Vertex} :
    v ∈ (envSidesGadget threeColoring env).1 ↔
      ∃ i, i < 3 ∧ (env >>> i &&& 1 == 1) = true ∧ v = Vertex.lit i := by
  show v ∈ (List.range 3).filterMap
      (fun i => if env >>> i &&& 1 == 1 then some (Vertex.lit i) else none) ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hif⟩
    rw [List.mem_range] at hi
    split at hif
    case isTrue h => exact ⟨i, hi, h, (Option.some.inj hif).symm⟩
    case isFalse => cases hif
  · rintro ⟨i, hi, hbit, rfl⟩
    exact ⟨i, List.mem_range.mpr hi, by rw [if_pos hbit]⟩

theorem mem_forbidden {env : Nat} {v : Vertex} :
    v ∈ (envSidesGadget threeColoring env).2 ↔
      ∃ i, i < 3 ∧ (env >>> i &&& 1 == 1) = false ∧ v = Vertex.lit i := by
  show v ∈ (List.range 3).filterMap
      (fun i => if env >>> i &&& 1 == 1 then none else some (Vertex.lit i)) ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hif⟩
    rw [List.mem_range] at hi
    split at hif
    case isTrue => cases hif
    case isFalse h =>
      exact ⟨i, hi, Bool.of_not_eq_true h, (Option.some.inj hif).symm⟩
  · rintro ⟨i, hi, hbit, rfl⟩
    have hne : ¬(env >>> i &&& 1 == 1) = true := by
      rw [hbit]
      exact Bool.false_ne_true
    exact ⟨i, List.mem_range.mpr hi, by rw [if_neg hne]⟩

theorem selected_nodup (env : Nat) :
    (envSidesGadget threeColoring env).1.Nodup := by
  show ((List.range 3).filterMap
      (fun i => if env >>> i &&& 1 == 1 then some (Vertex.lit i) else none)).Nodup
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro a a' b hb hb'
  rw [Option.mem_def] at hb hb'
  split at hb
  case isFalse => cases hb
  case isTrue =>
    have h1 : Vertex.lit a = b := Option.some.inj hb
    split at hb'
    case isFalse => cases hb'
    case isTrue =>
      have h2 : Vertex.lit a' = b := Option.some.inj hb'
      exact Vertex.lit.inj (h1.trans h2.symm)

theorem forbidden_nodup (env : Nat) :
    (envSidesGadget threeColoring env).2.Nodup := by
  show ((List.range 3).filterMap
      (fun i => if env >>> i &&& 1 == 1 then none else some (Vertex.lit i))).Nodup
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro a a' b hb hb'
  rw [Option.mem_def] at hb hb'
  split at hb
  case isTrue => cases hb
  case isFalse =>
    have h1 : Vertex.lit a = b := Option.some.inj hb
    split at hb'
    case isTrue => cases hb'
    case isFalse =>
      have h2 : Vertex.lit a' = b := Option.some.inj hb'
      exact Vertex.lit.inj (h1.trans h2.symm)

theorem map_selected_mem {U : Universe} {s : Perm} (hs : s ∈ perms)
    {env : Nat} (henv : env < 8) (u : Vertex) :
    u ∈ (envSidesGadget threeColoring env).1.map (U.act s) ↔
      u ∈ (envSidesGadget threeColoring (envAct s env)).1 := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi, hbit, rfl⟩ := mem_selected.mp hv
    refine mem_selected.mpr ⟨app s i, app_lt hs hi, ?_, rfl⟩
    rw [envAct_bit s hs env henv i hi]
    exact hbit
  · intro h
    obtain ⟨j, hj, hbit, rfl⟩ := mem_selected.mp h
    obtain ⟨i, hir, happ⟩ := app_surj s hs j hj
    have hi : i < 3 := List.mem_range.mp hir
    refine List.mem_map.mpr ⟨Vertex.lit i, mem_selected.mpr ⟨i, hi, ?_, rfl⟩, ?_⟩
    · rw [← envAct_bit s hs env henv i hi, happ]
      exact hbit
    · show Vertex.lit (app s i) = Vertex.lit j
      rw [happ]

theorem map_forbidden_mem {U : Universe} {s : Perm} (hs : s ∈ perms)
    {env : Nat} (henv : env < 8) (u : Vertex) :
    u ∈ (envSidesGadget threeColoring env).2.map (U.act s) ↔
      u ∈ (envSidesGadget threeColoring (envAct s env)).2 := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi, hbit, rfl⟩ := mem_forbidden.mp hv
    refine mem_forbidden.mpr ⟨app s i, app_lt hs hi, ?_, rfl⟩
    rw [envAct_bit s hs env henv i hi]
    exact hbit
  · intro h
    obtain ⟨j, hj, hbit, rfl⟩ := mem_forbidden.mp h
    obtain ⟨i, hir, happ⟩ := app_surj s hs j hj
    have hi : i < 3 := List.mem_range.mp hir
    refine List.mem_map.mpr ⟨Vertex.lit i, mem_forbidden.mpr ⟨i, hi, ?_, rfl⟩, ?_⟩
    · rw [← envAct_bit s hs env henv i hi, happ]
      exact hbit
    · show Vertex.lit (app s i) = Vertex.lit j
      rw [happ]

-- --------------------------------------------------- the row pin lists

/-- The pin list `colorsOk` builds for the gadget row at `env`. -/
def rowPins (parts : List Nat) (env : Nat) : List (Vertex × Nat) :=
  (anchorsOf parts.length (threeColoring.attach parts).1).zip [0, 1, 2]
    ++ (envSidesGadget threeColoring env).1.map ((·, 0))
    ++ (envSidesGadget threeColoring env).2.map ((·, 1))

theorem rowPins_eq (parts : List Nat) (env : Nat) :
    rowPins parts env =
      [(Vertex.aux parts.length 0, 0), (.aux (parts.length + 1) 0, 1),
       (.aux (parts.length + 2) 0, 2)]
        ++ (envSidesGadget threeColoring env).1.map ((·, 0))
        ++ (envSidesGadget threeColoring env).2.map ((·, 1)) := by
  unfold rowPins
  rw [attach_anchors]
  rfl

theorem map_fst_map_pair {β : Type} (c : Nat) (l : List β) :
    ((l.map ((·, c))).map (·.1)) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons]
    rw [ih]

theorem map_fst_map_act {σ : Vertex → Vertex} (l : List (Vertex × Nat)) :
    ((l.map fun q => (σ q.1, q.2)).map (·.1)) = (l.map (·.1)).map σ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons]
    rw [ih]

theorem rowPins_keys (parts : List Nat) (env : Nat) :
    (rowPins parts env).map (·.1)
      = [Vertex.aux parts.length 0, .aux (parts.length + 1) 0,
         .aux (parts.length + 2) 0]
        ++ (envSidesGadget threeColoring env).1
        ++ (envSidesGadget threeColoring env).2 := by
  rw [rowPins_eq, List.map_append, List.map_append, map_fst_map_pair,
    map_fst_map_pair]
  rfl

theorem rowPins_keys_nodup (parts : List Nat) (env : Nat) :
    ((rowPins parts env).map (·.1)).Nodup := by
  rw [rowPins_keys]
  have haux_ne : ∀ a b : Nat, a ≠ b → (Vertex.aux a 0 : Vertex) ≠ .aux b 0 := by
    intro a b hab h
    exact hab (Vertex.aux.inj h).1
  have hanchor : ([Vertex.aux parts.length 0, .aux (parts.length + 1) 0,
      .aux (parts.length + 2) 0] : List Vertex).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩⟩⟩
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact haux_ne _ _ (by omega) h
      rcases List.mem_cons.mp h with h | h
      · exact haux_ne _ _ (by omega) h
      · exact List.not_mem_nil h
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact haux_ne _ _ (by omega) h
      · exact List.not_mem_nil h
    · exact List.not_mem_nil
  have hanchor_lit : ∀ i : Nat, Vertex.lit i ∉
      ([Vertex.aux parts.length 0, .aux (parts.length + 1) 0,
        .aux (parts.length + 2) 0] : List Vertex) := by
    intro i h
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact List.not_mem_nil h
  refine (hanchor.append (selected_nodup env) ?_).append (forbidden_nodup env) ?_
  · intro x hx hsel
    obtain ⟨i, _, _, rfl⟩ := mem_selected.mp hsel
    exact hanchor_lit i hx
  · intro x hx hforb
    obtain ⟨i, hi, hbit0, rfl⟩ := mem_forbidden.mp hforb
    rcases List.mem_append.mp hx with hx | hx
    · exact hanchor_lit i hx
    · obtain ⟨i', _, hbit1, heq⟩ := mem_selected.mp hx
      have hii : i = i' := Vertex.lit.inj heq
      rw [← hii] at hbit1
      rw [hbit0] at hbit1
      cases hbit1

theorem rowPins_keys_mem (parts : List Nat) (env : Nat) :
    ∀ v ∈ (rowPins parts env).map (·.1),
      v ∈ (threeColoring.attach parts).1.vertices := by
  have hlen : (threeColoring.attach parts).1.parts.length = parts.length + 3 := by
    rw [attach_parts, List.length_append]
    rfl
  have hs0 : (threeColoring.attach parts).1.size parts.length = 1 :=
    attach_size parts (d := 0) (by omega)
  have hs1 : (threeColoring.attach parts).1.size (parts.length + 1) = 1 :=
    attach_size parts (by omega)
  have hs2 : (threeColoring.attach parts).1.size (parts.length + 2) = 1 :=
    attach_size parts (by omega)
  intro v hv
  rw [rowPins_keys] at hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · refine mem_vertices.mpr (Or.inr ?_)
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨parts.length, 0, by omega, by rw [hs0]; omega, rfl⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨parts.length + 1, 0, by omega, by rw [hs1]; omega, rfl⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨parts.length + 2, 0, by omega, by rw [hs2]; omega, rfl⟩
      · exact absurd hv (List.not_mem_nil)
    · obtain ⟨i, hi, _, rfl⟩ := mem_selected.mp hv
      exact mem_vertices.mpr (Or.inl ⟨i, hi, rfl⟩)
  · obtain ⟨i, hi, _, rfl⟩ := mem_forbidden.mp hv
    exact mem_vertices.mpr (Or.inl ⟨i, hi, rfl⟩)

theorem mem_map_pin_iff {β : Type} {σ : β → β} {l₁ l₂ : List β}
    (h : ∀ x, x ∈ l₁.map σ ↔ x ∈ l₂) (c : Nat) (p : β × Nat) :
    p ∈ (l₁.map ((·, c))).map (fun q => (σ q.1, q.2)) ↔ p ∈ l₂.map ((·, c)) := by
  rw [List.mem_map, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
    exact ⟨σ v, (h (σ v)).mp (List.mem_map.mpr ⟨v, hv, rfl⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, hveq⟩ := List.mem_map.mp ((h x).mpr hx)
    exact ⟨(v, c), List.mem_map.mpr ⟨v, hv, rfl⟩, by rw [hveq]⟩

theorem rowPins_map_mem {parts : List Nat} {s : Perm} (hs : s ∈ perms)
    {env : Nat} (henv : env < 8) (p : Vertex × Nat) :
    p ∈ (rowPins parts env).map
        (fun q => ((threeColoring.attach parts).1.act s q.1, q.2)) ↔
      p ∈ rowPins parts (envAct s env) := by
  have hsz0 : (threeColoring.attach parts).1.size parts.length = 1 :=
    attach_size parts (d := 0) (by omega)
  have hsz1 : (threeColoring.attach parts).1.size (parts.length + 1) = 1 :=
    attach_size parts (by omega)
  have hsz2 : (threeColoring.attach parts).1.size (parts.length + 2) = 1 :=
    attach_size parts (by omega)
  have hanch : (([(Vertex.aux parts.length 0, 0), (.aux (parts.length + 1) 0, 1),
      (.aux (parts.length + 2) 0, 2)] : List (Vertex × Nat)).map
        (fun q => ((threeColoring.attach parts).1.act s q.1, q.2)))
      = [(Vertex.aux parts.length 0, 0), (.aux (parts.length + 1) 0, 1),
         (.aux (parts.length + 2) 0, 2)] := by
    simp only [List.map_cons, List.map_nil, act_aux_one s 0 hsz0,
      act_aux_one s 0 hsz1, act_aux_one s 0 hsz2]
  rw [rowPins_eq, rowPins_eq, List.map_append, List.map_append, hanch,
    List.mem_append, List.mem_append, List.mem_append, List.mem_append]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ((mem_map_pin_iff
        (map_selected_mem (U := (threeColoring.attach parts).1) hs henv) 0 p).mp h))
    · exact Or.inr ((mem_map_pin_iff
        (map_forbidden_mem (U := (threeColoring.attach parts).1) hs henv) 1 p).mp h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ((mem_map_pin_iff
        (map_selected_mem (U := (threeColoring.attach parts).1) hs henv) 0 p).mpr h))
    · exact Or.inr ((mem_map_pin_iff
        (map_forbidden_mem (U := (threeColoring.attach parts).1) hs henv) 1 p).mpr h)

theorem rowPins_colorAt (parts : List Nat)
    (hU : (threeColoring.attach parts).1.legal) {s : Perm} (hs : s ∈ perms)
    {env : Nat} (henv : env < 8) (u : Vertex) :
    colorAt ((rowPins parts env).map fun q =>
        ((threeColoring.attach parts).1.act s q.1, q.2)) u
      = colorAt (rowPins parts (envAct s env)) u := by
  apply colorAt_congr_mem
  · rw [map_fst_map_act]
    refine (rowPins_keys_nodup parts env).map_on ?_
    intro x hx y hy hxy
    exact act_inj hU hs (rowPins_keys_mem parts env x hx)
      (rowPins_keys_mem parts env y hy) hxy
  · exact rowPins_keys_nodup parts _
  · exact rowPins_map_mem hs henv

-- ----------------------------------------------- the row-class reduction

/-- The instance `checkGadget` builds for the gadget row at `env`. -/
def rowInst (parts : List Nat) (g : List Edge) (env : Nat) : Instance Vertex :=
  { verts := (threeColoring.attach parts).1.vertices, edges := g,
    anchors := anchorsOf parts.length (threeColoring.attach parts).1,
    selected := (envSidesGadget threeColoring env).1,
    forbidden := (envSidesGadget threeColoring env).2 }

/-- Acting on the assignment of a row does not change the 3-coloring
    verdict on an S3-invariant graph. -/
theorem colorsOk_row_act (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6)
    {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ t ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge t e ∈ g)
    {s : Perm} (hs : s ∈ perms) {env : Nat} (henv : env < 8) :
    colorsOk (rowInst parts g (envAct s env)) = colorsOk (rowInst parts g env) := by
  have hU : (threeColoring.attach parts).1.legal := attach_legal parts hparts
  show colorable g (threeColoring.attach parts).1.vertices
      (rowPins parts (envAct s env))
    = colorable g (threeColoring.attach parts).1.vertices (rowPins parts env)
  have hedges : ∀ e ∈ g, e.1 ∈ (threeColoring.attach parts).1.vertices ∧
      e.2 ∈ (threeColoring.attach parts).1.vertices := fun e he =>
    ⟨(mem_edges (hg e he)).1, (mem_edges (hg e he)).2.1⟩
  have hne : ∀ e ∈ g, e.1 ≠ e.2 := fun e he => edges_ne (hg e he)
  have hloopg : ∀ a : Vertex, a ∉ adjTo g a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h
    · exact hne (a, a) h rfl
    · exact hne (a, a) h rfl
  have hnd := vertices_nodup (threeColoring.attach parts).1
  have hlr : ∀ v ∈ (threeColoring.attach parts).1.vertices,
      (threeColoring.attach parts).1.act (pinv s)
        ((threeColoring.attach parts).1.act s v) = v :=
    fun v hv => act_pinv_act hU hs hv
  have hkeys : ∀ p ∈ rowPins parts env,
      p.1 ∈ (threeColoring.attach parts).1.vertices := fun p hp =>
    rowPins_keys_mem parts env p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h1 := colorable_rename (σ := (threeColoring.attach parts).1.act s) hlr
    g (threeColoring.attach parts).1.vertices (rowPins parts env) hedges hne
    (fun _ hv => hv) hkeys hnd
  have h2 : ∀ v u : Vertex,
      u ∈ adjTo (g.map fun e => ((threeColoring.attach parts).1.act s e.1,
        (threeColoring.attach parts).1.act s e.2)) v ↔ u ∈ adjTo g v := by
    intro v u
    have hcomp : (g.map fun e => ((threeColoring.attach parts).1.act s e.1,
        (threeColoring.attach parts).1.act s e.2)).map normEdge
        = g.map ((threeColoring.attach parts).1.actEdge s) := by
      rw [List.map_map]
      rfl
    rw [← adjTo_map_normEdge, hcomp]
    exact adjTo_congr_mem (map_actEdge_mem hU hs hg hinv) v u
  have hnd₂ : ((threeColoring.attach parts).1.vertices.map
      ((threeColoring.attach parts).1.act s)).Nodup :=
    hnd.map_on fun x hx y hy hxy => by rw [← hlr x hx, hxy, hlr y hy]
  have hloopm : ∀ a : Vertex, a ∉ adjTo (g.map fun e =>
      ((threeColoring.attach parts).1.act s e.1,
        (threeColoring.attach parts).1.act s e.2)) a :=
    fun a ha => hloopg a ((h2 a a).mp ha)
  have h2' := colorable_congr_edges
    ((threeColoring.attach parts).1.vertices.map
      ((threeColoring.attach parts).1.act s))
    ((rowPins parts env).map fun q =>
      ((threeColoring.attach parts).1.act s q.1, q.2))
    hloopm hnd₂ h2
  have h3 := colorable_congr_verts g
    ((rowPins parts env).map fun q =>
      ((threeColoring.attach parts).1.act s q.1, q.2))
    hloopg hnd₂ hnd (map_act_mem hU hs)
  have h4 := colorable_congr_pins g (threeColoring.attach parts).1.vertices
    hloopg hnd (rowPins_colorAt parts hU hs henv)
  rw [← h4, ← h3, ← h2', h1]

theorem checkGadget_rows_eq (parts : List Nat) (g : List Edge)
    (symmetry : Bool) :
    checkGadget threeColoring (threeColoring.attach parts).1
        (anchorsOf parts.length (threeColoring.attach parts).1)
        (gadgetRows threeColoring symmetry) g
      = commonK threeColoring ((gadgetEnvs symmetry).map fun env =>
          (env != 0, rowInst parts g env)) := by
  unfold checkGadget gadgetRows
  rw [List.map_map]
  rfl

-- ---------------- the problem-generic reduction (equivariance interface)

/-- The row instance `checkGadget` builds for problem `P` at assignment
    `env` -- the problem-generic form of `rowInst`. -/
def rowInstP (P : Problem) (parts : List Nat) (g : List Edge) (env : Nat) :
    Instance Vertex :=
  { verts := (P.attach parts).1.vertices, edges := g,
    anchors := anchorsOf parts.length (P.attach parts).1,
    selected := (envSidesGadget P env).1,
    forbidden := (envSidesGadget P env).2 }

theorem rowInstP_threeColoring (parts : List Nat) (g : List Edge) (env : Nat) :
    rowInstP threeColoring parts g env = rowInst parts g env := rfl

theorem checkGadget_rows_eqP (P : Problem) (parts : List Nat) (g : List Edge)
    (symmetry : Bool) :
    checkGadget P (P.attach parts).1
        (anchorsOf parts.length (P.attach parts).1)
        (gadgetRows P symmetry) g
      = commonK P ((gadgetEnvs symmetry).map fun env =>
          (env != 0, rowInstP P parts g env)) := by
  unfold checkGadget gadgetRows
  rw [List.map_map]
  rfl

/-- The row-class reduction, problem-generically: if the problem's measure
    and exact columns are invariant under the S3 action on assignment rows,
    the four-class table and the eight-row table read the same budget. The
    invariance is the per-problem obligation (cf. `hkill` of
    `searchAux_complete`); 3-coloring discharges it below from
    `colorsOk_row_act`. -/
theorem checkGadget_symmetry (P : Problem) (parts : List Nat) {g : List Edge}
    (hmea : ∀ s ∈ perms, ∀ env, env < 8 →
      P.measure (rowInstP P parts g (envAct s env))
        = P.measure (rowInstP P parts g env))
    (hexa : ∀ s ∈ perms, ∀ env, env < 8 → ∀ k,
      P.exact (rowInstP P parts g (envAct s env)) k
        = P.exact (rowInstP P parts g env) k) :
    checkGadget P (P.attach parts).1
        (anchorsOf parts.length (P.attach parts).1)
        (gadgetRows P true) g
      = checkGadget P (P.attach parts).1
          (anchorsOf parts.length (P.attach parts).1)
          (gadgetRows P false) g := by
  rw [checkGadget_rows_eqP, checkGadget_rows_eqP]
  have henvs_t : gadgetEnvs true = [0, 1, 3, 7] := rfl
  have henvs_f : gadgetEnvs false = List.range 8 := rfl
  rw [henvs_t, henvs_f]
  apply commonK_eq_of_quotient
  · intro r hr
    obtain ⟨env, henv, rfl⟩ := List.mem_map.mp hr
    exact ⟨(env != 0, rowInstP P parts g env),
      List.mem_map.mpr ⟨env, reps_mem_range env henv, rfl⟩, rfl, rfl,
      fun _ => rfl⟩
  · intro r hr
    obtain ⟨env, henv, rfl⟩ := List.mem_map.mp hr
    have henv8 : env < 8 := List.mem_range.mp henv
    obtain ⟨rep, hrep, s, hs, hact⟩ := exists_class_rep env henv8
    have hrep8 : rep < 8 := reps_lt rep hrep
    refine ⟨(rep != 0, rowInstP P parts g rep),
      List.mem_map.mpr ⟨rep, hrep, rfl⟩, ?_, ?_, ?_⟩
    · rw [← hact]
      exact envAct_ne_zero s hs rep hrep8
    · show P.measure (rowInstP P parts g env)
        = P.measure (rowInstP P parts g rep)
      rw [← hact]
      exact hmea s hs rep hrep8
    · intro k
      show P.exact (rowInstP P parts g env) k
        = P.exact (rowInstP P parts g rep) k
      rw [← hact]
      exact hexa s hs rep hrep8 k

/-- `gadgetK` is its `checkGadget` when the negative-layer gate is open. -/
theorem gadgetK_eq (P : Problem) (parts : List Nat) (g : List Edge)
    (symmetry : Bool) (hneg : negLayerOk P (P.attach parts).1 = true) :
    gadgetK P parts g symmetry
      = checkGadget P (P.attach parts).1
          (anchorsOf parts.length (P.attach parts).1)
          (gadgetRows P symmetry) g := by
  unfold gadgetK
  rcases hUf : P.attach parts with ⟨U, forced⟩
  rw [hUf] at hneg
  have hneg' : negLayerOk P U = true := hneg
  simp [hneg']

/-- With the gate closed both tables are `none`. -/
theorem gadgetK_eq_none (P : Problem) (parts : List Nat) (g : List Edge)
    (symmetry : Bool) (hneg : negLayerOk P (P.attach parts).1 = false) :
    gadgetK P parts g symmetry = none := by
  unfold gadgetK
  rcases hUf : P.attach parts with ⟨U, forced⟩
  rw [hUf] at hneg
  have hneg' : negLayerOk P U = false := hneg
  simp [hneg']

/-- P4 headline, problem-generically (the symmetry-reduction theorem): for
    any problem whose measure and exact columns are invariant under the S3
    row action on the candidate graph, the symmetric four-class check and
    the raw eight-row check agree -- `gadgetK` with symmetry on equals
    `gadgetK` with symmetry off. Symmetric-only sweeps are thereby licensed
    for every such problem, not just 3-coloring. -/
theorem gadgetK_s3_symmetry_reduction (P : Problem) (parts : List Nat)
    {g : List Edge}
    (hmea : ∀ s ∈ perms, ∀ env, env < 8 →
      P.measure (rowInstP P parts g (envAct s env))
        = P.measure (rowInstP P parts g env))
    (hexa : ∀ s ∈ perms, ∀ env, env < 8 → ∀ k,
      P.exact (rowInstP P parts g (envAct s env)) k
        = P.exact (rowInstP P parts g env) k) :
    gadgetK P parts g true = gadgetK P parts g false := by
  cases hneg : negLayerOk P (P.attach parts).1 with
  | false => rw [gadgetK_eq_none P parts g true hneg,
                 gadgetK_eq_none P parts g false hneg]
  | true =>
    rw [gadgetK_eq P parts g true hneg, gadgetK_eq P parts g false hneg]
    exact checkGadget_symmetry P parts hmea hexa

-- ------------------------------ the 3-coloring discharge of the interface

/-- 3-coloring's measure column is invariant under the row action on an
    S3-invariant graph (from `colorsOk_row_act`). -/
theorem threeColoring_rowMeasure_act (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6)
    {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ t ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge t e ∈ g) :
    ∀ s ∈ perms, ∀ env, env < 8 →
      threeColoring.measure (rowInstP threeColoring parts g (envAct s env))
        = threeColoring.measure (rowInstP threeColoring parts g env) := by
  intro s hs env henv
  have hco := colorsOk_row_act parts hparts hg hinv hs henv
  rw [rowInstP_threeColoring, rowInstP_threeColoring]
  simp only [threeColoring, feasibility, hco]

/-- 3-coloring's exact column is invariant likewise. -/
theorem threeColoring_rowExact_act (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6)
    {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ t ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge t e ∈ g) :
    ∀ s ∈ perms, ∀ env, env < 8 → ∀ k,
      threeColoring.exact (rowInstP threeColoring parts g (envAct s env)) k
        = threeColoring.exact (rowInstP threeColoring parts g env) k := by
  intro s hs env henv k
  have hco := colorsOk_row_act parts hparts hg hinv hs henv
  rw [rowInstP_threeColoring, rowInstP_threeColoring]
  simp only [threeColoring, feasibility, hco]

/-- The 3-coloring instance of the reduction, on the original hypotheses:
    S3-invariance of the graph over legal parts. -/
theorem gadgetK_s3_symmetry_reduction_threeColoring (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6)
    {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ s ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge s e ∈ g) :
    gadgetK threeColoring parts g true = gadgetK threeColoring parts g false :=
  gadgetK_s3_symmetry_reduction threeColoring parts
    (threeColoring_rowMeasure_act parts hparts hg hinv)
    (threeColoring_rowExact_act parts hparts hg hinv)

-- ------------------------- every graph of the symmetric walk qualifies

theorem graphAt_props {U : Universe} {base : List Edge}
    {free : List (List Edge)} (hbase_sub : ∀ e ∈ base, e ∈ U.edges)
    (hbase_cl : ∀ s ∈ perms, ∀ e ∈ base, U.actEdge s e ∈ base)
    (hfree : ∀ o ∈ free, (∀ e ∈ o, e ∈ U.edges) ∧
      ∀ s ∈ perms, ∀ e ∈ o, U.actEdge s e ∈ o) (mask : Nat) :
    (∀ e ∈ graphAt base free mask, e ∈ U.edges) ∧
      ∀ s ∈ perms, ∀ e ∈ graphAt base free mask,
        U.actEdge s e ∈ graphAt base free mask := by
  have hmem : ∀ e : Edge, e ∈ graphAt base free mask ↔
      e ∈ base ∨ ∃ o, o ∈ bitSubset mask free ∧ e ∈ o := by
    intro e
    unfold graphAt
    rw [graphAt_selector free mask, List.mem_append, List.mem_flatten]
  constructor
  · intro e he
    rcases (hmem e).mp he with h | ⟨o, ho, heo⟩
    · exact hbase_sub e h
    · exact (hfree o ((bitSubset_sublist mask free).subset ho)).1 e heo
  · intro s hs e he
    rcases (hmem e).mp he with h | ⟨o, ho, heo⟩
    · exact (hmem _).mpr (Or.inl (hbase_cl s hs e h))
    · exact (hmem _).mpr (Or.inr ⟨o, ho,
        (hfree o ((bitSubset_sublist mask free).subset ho)).2 s hs e heo⟩)

/-- Every graph the symmetric walk enumerates lives inside the edge list
    and is S3-invariant. -/
theorem graphs_symmetric_props {U : Universe} (hU : U.legal)
    (hll : U.litLit = false) (forced : List Edge) :
    ∀ g ∈ U.graphs (symmetry := true) (forced := forced),
      (∀ e ∈ g, e ∈ U.edges) ∧
        ∀ s ∈ perms, ∀ e ∈ g, U.actEdge s e ∈ g := by
  have hsw : U.switches true = U.orbits := rfl
  intro g hg
  unfold Universe.graphs at hg
  obtain ⟨mask, _, rfl⟩ := List.mem_map.mp hg
  refine graphAt_props ?_ ?_ ?_ mask
  · intro e he
    obtain ⟨o, ho, heo⟩ := List.mem_flatten.mp he
    have ho' : o ∈ U.orbits := hsw ▸ (List.mem_filter.mp ho).1
    exact (orbit_switch_props hU hll ho').1 e heo
  · intro s hs e he
    obtain ⟨o, ho, heo⟩ := List.mem_flatten.mp he
    have ho' : o ∈ U.orbits := hsw ▸ (List.mem_filter.mp ho).1
    exact List.mem_flatten.mpr
      ⟨o, ho, (orbit_switch_props hU hll ho').2 s hs e heo⟩
  · intro o ho
    have ho' : o ∈ U.orbits := hsw ▸ (List.mem_filter.mp ho).1
    exact orbit_switch_props hU hll ho'

/-- P4 corollary: an empty symmetric sweep certifies the raw eight-row
    rejection across the whole symmetric candidate space -- the paper's
    negative claims need only the orbit-quotient sweep even against the
    raw table. -/
theorem searchSlice_symmetric_covers_raw (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6)
    (hfound : (searchSlice threeColoring parts true).2.found = []) :
    ∀ g ∈ (threeColoring.attach parts).1.graphs (symmetry := true)
        (forced := (threeColoring.attach parts).2),
      gadgetK threeColoring parts g false = none := by
  intro g hg
  have hU : (threeColoring.attach parts).1.legal := attach_legal parts hparts
  have hll : (threeColoring.attach parts).1.litLit = false := rfl
  obtain ⟨hsub, hcl⟩ := graphs_symmetric_props hU hll
    (threeColoring.attach parts).2 g hg
  rw [← gadgetK_s3_symmetry_reduction_threeColoring parts hparts hsub hcl]
  exact searchSlice_exhaustive_threeColoring_graphs parts true hfound g hg

end Atlas
