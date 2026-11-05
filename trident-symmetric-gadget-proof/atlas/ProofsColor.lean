import atlas.ProofsColorK
/-!
  P4 stage 2: reflection of the 3-coloring backtracker.

  `colorableGo` is characterized by an existence statement (`SpecExt`):
  the run succeeds iff a choice function assigns every remaining vertex
  a pin-respecting color with no conflict along any edge into the
  combined assignment. Downstream, invariance of the verifier under
  vertex-list and pin-list permutation is a corollary at the spec level
  (here), where only membership matters; the renaming invariance used by
  the symmetry reduction is derived from the same spec in
  `atlas/ProofsSym.lean` (`colorable_rename`). Soundness needs the graph
  to be loop-free (`hloop`), completeness does not.

  Since the review round of 2026-09-02 the reflection is the k = 3
  instance of the palette-generic one (ProofsColorK): `SpecExt` is
  `SpecExtK 3` up to unfolding (`SpecExt_iff_SpecExtK3`) and the two
  directions are read off `colorableGoK_sound/_complete` through the
  kernel bridge -- no second copy of the induction.
-/

namespace Atlas

open List

variable {α : Type} [BEq α] [LawfulBEq α]

/-- A legal color choice at `v`: the pin if pinned, any of 0/1/2 else. -/
def pinOk (pins : List (α × Nat)) (v : α) (c : Nat) : Prop :=
  match colorAt pins v with
  | some cp => c = cp
  | none => c < 3

/-- The spec: a pin-respecting conflict-free extension over `rest`. -/
def SpecExt (edges : List (α × α)) (pins : List (α × Nat)) (rest : List α)
    (assign : List (α × Nat)) (f : α → Nat) : Prop :=
  (∀ v ∈ rest, pinOk pins v (f v)) ∧
  (∀ v ∈ rest, ∀ u ∈ adjTo edges v,
    combined rest assign f u ≠ some (f v))

-- ------------------------------------------------------------- reflection

omit [LawfulBEq α] in
/-- `pinOk` is the k = 3 instance of `pinOkK`. -/
theorem pinOk_iff_pinOkK3 (pins : List (α × Nat)) (v : α) (c : Nat) :
    pinOk pins v c ↔ pinOkK 3 pins v c := by
  unfold pinOk pinOkK
  cases colorAt pins v <;> exact Iff.rfl

/-- `SpecExt` is the k = 3 instance of `SpecExtK`. -/
theorem SpecExt_iff_SpecExtK3 (edges : List (α × α)) (pins : List (α × Nat))
    (rest : List α) (assign : List (α × Nat)) (f : α → Nat) :
    SpecExt edges pins rest assign f ↔ SpecExtK 3 edges pins rest assign f := by
  unfold SpecExt SpecExtK
  constructor
  · rintro ⟨hpin, hconf⟩
    exact ⟨fun v hv => (pinOk_iff_pinOkK3 pins v (f v)).mp (hpin v hv), hconf⟩
  · rintro ⟨hpin, hconf⟩
    exact ⟨fun v hv => (pinOk_iff_pinOkK3 pins v (f v)).mpr (hpin v hv), hconf⟩

/-- Soundness: a successful run yields a spec witness (the k = 3 instance
    of `colorableGoK_sound`). -/
theorem colorableGo_sound (edges : List (α × α)) (pins : List (α × Nat))
    (hloop : ∀ a : α, a ∉ adjTo edges a) :
    ∀ (rest : List α) (assign : List (α × Nat)), rest.Nodup →
      (∀ v ∈ rest, colorAt assign v = none) →
      colorableGo edges pins rest assign = true →
      ∃ f, SpecExt edges pins rest assign f := by
  intro rest assign hnd hdisj hrun
  rw [colorableGo_eq_colorableGoK3] at hrun
  obtain ⟨f, hf⟩ := colorableGoK_sound 3 edges pins hloop rest assign hnd hdisj hrun
  exact ⟨f, (SpecExt_iff_SpecExtK3 _ _ _ _ _).mpr hf⟩
/-- Completeness: a spec witness forces the run to succeed (the k = 3
    instance of `colorableGoK_complete`). -/
theorem colorableGo_complete (edges : List (α × α)) (pins : List (α × Nat)) :
    ∀ (rest : List α) (assign : List (α × Nat)), rest.Nodup →
      (∀ v ∈ rest, colorAt assign v = none) →
      (∃ f, SpecExt edges pins rest assign f) →
      colorableGo edges pins rest assign = true := by
  intro rest assign hnd hdisj ⟨f, hf⟩
  rw [colorableGo_eq_colorableGoK3]
  exact colorableGoK_complete 3 edges pins rest assign hnd hdisj
    ⟨f, (SpecExt_iff_SpecExtK3 _ _ _ _ _).mp hf⟩
/-- The reflection: the backtracker answers exactly the existence of a
    pin-respecting proper extension. -/
theorem colorable_iff_spec (edges : List (α × α)) (verts : List α)
    (pins : List (α × Nat)) (hloop : ∀ a : α, a ∉ adjTo edges a)
    (hnd : verts.Nodup) :
    colorable edges verts pins = true ↔
      ∃ f, SpecExt edges pins verts [] f := by
  constructor
  · exact colorableGo_sound edges pins hloop verts []
      hnd (fun v _ => colorAt_nil v)
  · exact colorableGo_complete edges pins verts []
      hnd (fun v _ => colorAt_nil v)

-- --------------------------------------- membership-level invariances

/-- The spec sees the vertex list only through membership. -/
theorem SpecExt_congr_verts {edges : List (α × α)} {pins : List (α × Nat)}
    {verts₁ verts₂ : List α} (h : ∀ u : α, u ∈ verts₁ ↔ u ∈ verts₂)
    {f : α → Nat} (hs : SpecExt edges pins verts₁ [] f) :
    SpecExt edges pins verts₂ [] f := by
  obtain ⟨hpin, hconf⟩ := hs
  classical
  refine ⟨fun v hv => hpin v ((h v).mpr hv), ?_⟩
  intro v hv u hu
  have := hconf v ((h v).mpr hv) u hu
  unfold combined at this ⊢
  by_cases hu1 : u ∈ verts₁
  · rw [if_pos ((h u).mp hu1)]
    rw [if_pos hu1] at this
    exact this
  · rw [if_neg (fun hc => hu1 ((h u).mpr hc))]
    rw [if_neg hu1] at this
    exact this

/-- The verifier is invariant under permutation (indeed any
    membership-preserving change) of the vertex list. -/
theorem colorable_congr_verts (edges : List (α × α)) (pins : List (α × Nat))
    {verts₁ verts₂ : List α} (hloop : ∀ a : α, a ∉ adjTo edges a)
    (hnd₁ : verts₁.Nodup) (hnd₂ : verts₂.Nodup)
    (h : ∀ u : α, u ∈ verts₁ ↔ u ∈ verts₂) :
    colorable edges verts₁ pins = colorable edges verts₂ pins := by
  have h12 := colorable_iff_spec edges verts₁ pins hloop hnd₁
  have h21 := colorable_iff_spec edges verts₂ pins hloop hnd₂
  cases hc : colorable edges verts₂ pins
  · cases hc1 : colorable edges verts₁ pins
    · rfl
    · obtain ⟨f, hf⟩ := h12.mp hc1
      have := h21.mpr ⟨f, SpecExt_congr_verts h hf⟩
      rw [hc] at this
      cases this
  · obtain ⟨f, hf⟩ := h21.mp hc
    exact h12.mpr ⟨f, SpecExt_congr_verts (fun u => (h u).symm) hf⟩

/-- The spec sees the pin list only through `colorAt`. -/
theorem SpecExt_congr_pins {edges : List (α × α)}
    {pins₁ pins₂ : List (α × Nat)} {verts : List α}
    (h : ∀ u : α, colorAt pins₁ u = colorAt pins₂ u) {f : α → Nat}
    (hs : SpecExt edges pins₁ verts [] f) :
    SpecExt edges pins₂ verts [] f := by
  obtain ⟨hpin, hconf⟩ := hs
  refine ⟨fun v hv => ?_, hconf⟩
  have := hpin v hv
  unfold pinOk at this ⊢
  rw [← h v]
  exact this

theorem colorable_congr_pins (edges : List (α × α)) (verts : List α)
    {pins₁ pins₂ : List (α × Nat)} (hloop : ∀ a : α, a ∉ adjTo edges a)
    (hnd : verts.Nodup) (h : ∀ u : α, colorAt pins₁ u = colorAt pins₂ u) :
    colorable edges verts pins₁ = colorable edges verts pins₂ := by
  have h1 := colorable_iff_spec edges verts pins₁ hloop hnd
  have h2 := colorable_iff_spec edges verts pins₂ hloop hnd
  cases hc : colorable edges verts pins₂
  · cases hc1 : colorable edges verts pins₁
    · rfl
    · obtain ⟨f, hf⟩ := h1.mp hc1
      have := h2.mpr ⟨f, SpecExt_congr_pins h hf⟩
      rw [hc] at this
      cases this
  · obtain ⟨f, hf⟩ := h2.mp hc
    exact h1.mpr ⟨f, SpecExt_congr_pins (fun u => (h u).symm) hf⟩

end Atlas
