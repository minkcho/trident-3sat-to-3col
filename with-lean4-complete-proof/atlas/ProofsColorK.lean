import atlas.Problems.KColoring
/-!
  The palette-generic coloring kernel, reflected and shown antitone -- the
  base of the coloring developments (P7-2a, made the base in the review
  round of 2026-09-02).

  `colorableGoK k` is the backtracker with the palette `List.range k`;
  the 3-coloring kernel `colorableGo` is its k = 3 instance
  (`colorableGo_eq_colorableGoK3`). This file owns everything
  palette-free -- `colorAt`, `combined`, `combined_shift`, `mem_adjTo`,
  `adjTo_symm`, `adjTo_sublist`, `any_mono` -- and proves, once for every
  k, antitonicity in the edge set (`colorableGoK_antitone`) and the
  reflection into the existence spec `SpecExtK` (`colorableGoK_sound`,
  `colorableGoK_complete`, `colorableK_iff_spec`). The k = 2 instance is
  (in the full line) bipartization's `twoColorable_iff_spec`; the k = 3 instance is derived in
  ProofsPrune (`colorableGo_antitone`) and ProofsColor (`colorableGo_sound`,
  `colorableGo_complete`) through the bridge, so the 3-coloring
  development no longer carries its own copies of these proofs.
-/

namespace Atlas

open List

variable {α : Type} [BEq α] [LawfulBEq α]

/-- The color an assignment list gives a vertex. -/
def colorAt (asg : List (α × Nat)) (u : α) : Option Nat :=
  (asg.find? (·.1 == u)).map (·.2)

/-- The combined coloring: the choice function on the remaining
    vertices, the accumulated assignment elsewhere. -/
def combined (rest : List α) (assign : List (α × Nat))
    (f : α → Nat) (u : α) : Option Nat :=
  if u ∈ rest then some (f u) else colorAt assign u

-- ------------------------------------------------------------ small lemmas

omit [LawfulBEq α] in
theorem colorAt_nil (u : α) : colorAt ([] : List (α × Nat)) u = none := rfl

omit [LawfulBEq α] in
theorem colorAt_cons {v u : α} {c : Nat} {asg : List (α × Nat)} :
    colorAt ((v, c) :: asg) u = if v == u then some c else colorAt asg u := by
  by_cases h : v == u <;> simp [colorAt, h]

theorem mem_adjTo {edges : List (α × α)} {v u : α} :
    u ∈ adjTo edges v ↔ (v, u) ∈ edges ∨ (u, v) ∈ edges := by
  unfold adjTo
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, b⟩, hab, hif⟩
    dsimp only at hif
    by_cases ha : a == v
    · rw [if_pos ha] at hif
      cases hif
      rw [eq_of_beq ha] at hab
      exact Or.inl hab
    · rw [if_neg ha] at hif
      by_cases hb : b == v
      · rw [if_pos hb] at hif
        cases hif
        rw [eq_of_beq hb] at hab
        exact Or.inr hab
      · rw [if_neg hb] at hif
        cases hif
  · rintro (h | h)
    · exact ⟨(v, u), h, by simp⟩
    · refine ⟨(u, v), h, ?_⟩
      dsimp only
      by_cases hu : u == v
      · rw [if_pos hu, eq_of_beq hu]
      · rw [if_neg hu, if_pos (by simp)]

theorem adjTo_symm {edges : List (α × α)} {v u : α}
    (h : u ∈ adjTo edges v) : v ∈ adjTo edges u := by
  rcases mem_adjTo.mp h with h' | h'
  · exact mem_adjTo.mpr (Or.inr h')
  · exact mem_adjTo.mpr (Or.inl h')

/-- The one shift identity both directions of the reflection rest on:
    moving the head vertex from the remaining list into the assignment
    leaves the combined coloring unchanged. -/
theorem combined_shift {v : α} {rest : List α} {assign : List (α × Nat)}
    {f f' : α → Nat} {c : Nat} (hvr : v ∉ rest) (hfv : f v = c)
    (hff' : ∀ u ∈ rest, f u = f' u) (u : α) :
    combined (v :: rest) assign f u = combined rest ((v, c) :: assign) f' u := by
  unfold combined
  by_cases hu : u ∈ rest
  · rw [if_pos (List.mem_cons_of_mem _ hu), if_pos hu, hff' u hu]
  · by_cases huv : u = v
    · subst huv
      rw [if_pos (List.mem_cons_self ..), if_neg hu, colorAt_cons,
        if_pos (by simp), hfv]
    · have hnotin : u ∉ v :: rest := by
        intro h
        rcases List.mem_cons.mp h with h | h
        · exact huv h
        · exact hu h
      have hbne : ¬ (v == u) = true := by
        intro hbeq
        exact huv (eq_of_beq hbeq).symm
      rw [if_neg hnotin, if_neg hu, colorAt_cons, if_neg hbne]

omit [LawfulBEq α] in
theorem adjTo_sublist {edges edges' : List (α × α)}
    (h : edges <+ edges') (v : α) : adjTo edges v <+ adjTo edges' v :=
  h.filterMap _

omit [BEq α] [LawfulBEq α] in
theorem any_mono {l l' : List α} (h : l <+ l') {p : α → Bool}
    (ha : l.any p = true) : l'.any p = true := by
  obtain ⟨x, hx, hpx⟩ := List.any_eq_true.mp ha
  exact List.any_eq_true.mpr ⟨x, h.subset hx, hpx⟩

/-- A legal color choice at `v`: the pin if pinned, any of 0..k-1 else. -/
def pinOkK (k : Nat) (pins : List (α × Nat)) (v : α) (c : Nat) : Prop :=
  match colorAt pins v with
  | some cp => c = cp
  | none => c < k

/-- The spec: a pin-respecting conflict-free `k`-extension over `rest`. -/
def SpecExtK (k : Nat) (edges : List (α × α)) (pins : List (α × Nat))
    (rest : List α) (assign : List (α × Nat)) (f : α → Nat) : Prop :=
  (∀ v ∈ rest, pinOkK k pins v (f v)) ∧
  (∀ v ∈ rest, ∀ u ∈ adjTo edges v,
    combined rest assign f u ≠ some (f v))

-- ---------------------------------------------------------- antitonicity

omit [LawfulBEq α] in
/-- The palette-generic kernel is antitone in the edge set: a proper
    coloring under more edges is proper under fewer. -/
theorem colorableGoK_antitone {k : Nat} {edges edges' : List (α × α)}
    (h : edges <+ edges') (pins : List (α × Nat)) :
    ∀ (rest : List α) (assign : List (α × Nat)),
      colorableGoK k edges' pins rest assign = true →
      colorableGoK k edges pins rest assign = true := by
  intro rest
  induction rest with
  | nil => intro _ _; rfl
  | cons v rest ih =>
    intro assign hc
    simp only [colorableGoK] at hc ⊢
    obtain ⟨c, hcmem, hcbody⟩ := List.any_eq_true.mp hc
    refine List.any_eq_true.mpr ⟨c, hcmem, ?_⟩
    split at hcbody
    · cases hcbody
    · next hb' =>
      split
      · next hconf => exact absurd (any_mono (adjTo_sublist h v) hconf) hb'
      · next => exact ih _ hcbody

omit [LawfulBEq α] in
theorem colorableK_antitone {k : Nat} {edges edges' : List (α × α)}
    (h : edges <+ edges') (verts : List α) (pins : List (α × Nat)) :
    colorableK k edges' verts pins = true →
    colorableK k edges verts pins = true :=
  colorableGoK_antitone h pins verts []

-- ------------------------------------------------------------- reflection

/-- Soundness: a successful run yields a spec witness. -/
theorem colorableGoK_sound (k : Nat) (edges : List (α × α))
    (pins : List (α × Nat)) (hloop : ∀ a : α, a ∉ adjTo edges a) :
    ∀ (rest : List α) (assign : List (α × Nat)), rest.Nodup →
      (∀ v ∈ rest, colorAt assign v = none) →
      colorableGoK k edges pins rest assign = true →
      ∃ f, SpecExtK k edges pins rest assign f := by
  intro rest
  induction rest with
  | nil =>
    intro assign _ _ _
    refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro v hv <;> cases hv
  | cons v rest ih =>
    intro assign hnd hdisj hrun
    obtain ⟨hvr, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [colorableGoK] at hrun
    obtain ⟨c, hc, hcond⟩ := List.any_eq_true.mp hrun
    have hconf : ((adjTo edges v).any fun u =>
        ((assign.find? (·.1 == u)).map (·.2)) == some c) = false := by
      cases h : (adjTo edges v).any fun u =>
          ((assign.find? (·.1 == u)).map (·.2)) == some c
      · rfl
      · rw [h] at hcond
        simp at hcond
    rw [hconf] at hcond
    simp only [Bool.false_eq_true, if_false] at hcond
    have hdisj' : ∀ w ∈ rest, colorAt ((v, c) :: assign) w = none := by
      intro w hw
      rw [colorAt_cons, if_neg, hdisj w (List.mem_cons_of_mem _ hw)]
      intro h
      exact hvr ((eq_of_beq h) ▸ hw)
    obtain ⟨f', hpin', hconf'⟩ := ih ((v, c) :: assign) hnd' hdisj' hcond
    classical
    refine ⟨fun u => if u = v then c else f' u, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · simp only
        unfold pinOkK
        revert hc
        unfold colorAt
        cases hp : (pins.find? (·.1 == w)).map (·.2) with
        | some cp =>
          intro hc
          simp only [List.mem_singleton] at hc
          exact hc
        | none =>
          intro hc
          exact List.mem_range.mp hc
      · have hne : w ≠ v := fun h => hvr (h ▸ hw')
        simp only [if_neg hne]
        exact hpin' w hw'
    · intro w hw u hu
      have hshift := combined_shift (assign := assign)
        (f := fun u => if u = v then c else f' u)
        (f' := f') (c := c) hvr (by simp)
        (fun u hu => by
          have : u ≠ v := fun h => hvr (h ▸ hu)
          simp [this]) u
      rw [hshift]
      rcases List.mem_cons.mp hw with rfl | hw'
      · simp only
        by_cases huv : u = w
        · exact absurd hu (huv ▸ hloop w)
        · by_cases hur : u ∈ rest
          · have h := hconf' u hur w (adjTo_symm hu)
            unfold combined at h ⊢
            rw [if_pos hur]
            rw [if_neg hvr, colorAt_cons, if_pos (by simp)] at h
            intro hcontra
            exact h ((Option.some.inj hcontra) ▸ rfl)
          · unfold combined
            rw [if_neg hur, colorAt_cons, if_neg (by
              intro hbeq
              exact huv (eq_of_beq hbeq).symm)]
            have := List.any_eq_false.mp hconf u hu
            intro hcontra
            apply this
            rw [show ((assign.find? (·.1 == u)).map (·.2)) = colorAt assign u
              from rfl, hcontra]
            simp
      · have hne : w ≠ v := fun h => hvr (h ▸ hw')
        simp only [if_neg hne]
        exact hconf' w hw' u hu

/-- Completeness: a spec witness forces the run to succeed. -/
theorem colorableGoK_complete (k : Nat) (edges : List (α × α))
    (pins : List (α × Nat)) :
    ∀ (rest : List α) (assign : List (α × Nat)), rest.Nodup →
      (∀ v ∈ rest, colorAt assign v = none) →
      (∃ f, SpecExtK k edges pins rest assign f) →
      colorableGoK k edges pins rest assign = true := by
  intro rest
  induction rest with
  | nil =>
    intro assign _ _ _
    rfl
  | cons v rest ih =>
    intro assign hnd hdisj ⟨f, hpin, hconf⟩
    obtain ⟨hvr, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [colorableGoK]
    refine List.any_eq_true.mpr ⟨f v, ?_, ?_⟩
    · have := hpin v (List.mem_cons_self ..)
      unfold pinOkK at this
      revert this
      unfold colorAt
      cases hp : (pins.find? (·.1 == v)).map (·.2) with
      | some cp =>
        intro h
        rw [h]
        exact List.mem_singleton.mpr rfl
      | none =>
        intro h
        exact List.mem_range.mpr h
    · have hcheck : ((adjTo edges v).any fun u =>
          ((assign.find? (·.1 == u)).map (·.2)) == some (f v)) = false := by
      -- every neighbor is either still unassigned or spec-clean
        refine List.any_eq_false.mpr ?_
        intro u hu
        have hspec := hconf v (List.mem_cons_self ..) u hu
        unfold combined at hspec
        by_cases hur : u ∈ v :: rest
        · rw [show ((assign.find? (·.1 == u)).map (·.2)) = colorAt assign u
            from rfl, hdisj u hur]
          simp
        · rw [if_neg hur] at hspec
          rw [show ((assign.find? (·.1 == u)).map (·.2)) = colorAt assign u
            from rfl]
          cases hca : colorAt assign u with
          | none => simp
          | some d =>
            rw [hca] at hspec
            simp only [beq_iff_eq]
            intro hcontra
            exact hspec (hcontra ▸ rfl)
      rw [hcheck]
      simp only [Bool.false_eq_true, if_false]
      refine ih ((v, f v) :: assign) hnd' ?_ ⟨f, ?_, ?_⟩
      · intro w hw
        rw [colorAt_cons, if_neg, hdisj w (List.mem_cons_of_mem _ hw)]
        intro h
        exact hvr ((eq_of_beq h) ▸ hw)
      · exact fun w hw => hpin w (List.mem_cons_of_mem _ hw)
      · intro w hw u hu
        have hshift := combined_shift (assign := assign) (f := f) (f' := f)
          (c := f v) hvr rfl
          (fun _ _ => rfl) u
        rw [← hshift]
        exact hconf w (List.mem_cons_of_mem _ hw) u hu

/-- The reflection: the palette-generic backtracker answers exactly the
    existence of a pin-respecting proper `k`-extension. -/
theorem colorableK_iff_spec (k : Nat) (edges : List (α × α))
    (verts : List α) (pins : List (α × Nat))
    (hloop : ∀ a : α, a ∉ adjTo edges a) (hnd : verts.Nodup) :
    colorableK k edges verts pins = true ↔
      ∃ f, SpecExtK k edges pins verts [] f := by
  constructor
  · exact colorableGoK_sound k edges pins hloop verts []
      hnd (fun v _ => colorAt_nil v)
  · exact colorableGoK_complete k edges pins verts []
      hnd (fun v _ => colorAt_nil v)


-- --------------------------------------------- the 3-coloring instance

omit [LawfulBEq α] in
/-- Bridge: the 3-coloring kernel is the k = 3 instance of the generic
    kernel; ProofsPrune and ProofsColor derive their antitonicity and
    reflection through it. -/
theorem colorableGo_eq_colorableGoK3 (edges : List (α × α))
    (pins : List (α × Nat)) :
    ∀ (rest : List α) (assign : List (α × Nat)),
      colorableGo edges pins rest assign
        = colorableGoK 3 edges pins rest assign := by
  intro rest
  induction rest with
  | nil => intro _; rfl
  | cons v rest ih =>
    intro assign
    simp only [colorableGo, colorableGoK]
    rw [show List.range 3 = [0, 1, 2] from rfl]
    congr 1
    funext c
    exact ite_congr rfl (fun _ => rfl) (fun _ => ih ((v, c) :: assign))

omit [LawfulBEq α] in
theorem colorable_eq_colorableK3 (edges : List (α × α)) (verts : List α)
    (pins : List (α × Nat)) :
    colorable edges verts pins = colorableK 3 edges verts pins :=
  colorableGo_eq_colorableGoK3 edges pins verts []

end Atlas
