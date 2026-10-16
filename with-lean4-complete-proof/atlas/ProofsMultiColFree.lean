import atlas.ProofsMultiCol
/-!
  P6-5: the pin-free form of the 3-coloring reduction.

  `multiK_threeColoring_iff` (P6-2) is the engine's verdict: every pinned
  row of the assembly is colorable iff its assignment satisfies the
  formula. This file removes the row pins. A proper 3-coloring of the
  assembled graph that respects only the palette (anchors T, F, B) exists
  iff some row is colorable (`colorable_assembly_iff_row`): the layer
  edges force every literal-layer pair onto {T, F} (`layer_forces`), and
  the pair colors read off an assignment (`exists_env_of_bits`); in the
  other direction a row coloring is a palette coloring
  (`SpecExt_of_pins_sub`). Composed with the row semantics of P6-2:
  `colorable_assembly_iff_sat`, and for the sweep's own find
  `trident_colorable_iff` -- "the trident assembly, with its palette
  pinned, is 3-colorable iff the formula is satisfiable", the textbook
  statement of the reduction. (Review 2026-09-02, M1.)
-/

namespace Atlas

open List

-- (`bit_eq_testBit` and `exists_env_of_bits` -- the framework's bit test is
-- `Nat.testBit`, and every bit pattern is some `env < 2^n` -- live in
-- ProofsKits.)

-- ---------------------------------------------------- palette-only pins

/-- The palette alone: anchors T, F, B pinned to 0, 1, 2. -/
def palettePins : List (MVertex × Nat) :=
  [(MVertex.anchor 0, 0), (.anchor 1, 1), (.anchor 2, 2)]

theorem rowPinsM_eq_palette_append (clauses : List ClauseSpec) (env : Nat) :
    rowPinsM clauses env = palettePins ++
      (((List.range (varCount clauses)).map fun v =>
          if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v).map ((·, 0))
        ++ ((List.range (varCount clauses)).map fun v =>
          if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v).map ((·, 1))) := rfl

theorem colorAt_append_left {pins₁ pins₂ : List (MVertex × Nat)} {v : MVertex}
    {c : Nat} (h : colorAt pins₁ v = some c) :
    colorAt (pins₁ ++ pins₂) v = some c := by
  unfold colorAt at h ⊢
  rw [List.find?_append]
  cases hf : pins₁.find? (·.1 == v) with
  | none => rw [hf] at h; cases h
  | some p => rw [hf] at h; simpa using h

theorem palettePins_val : ∀ p ∈ palettePins, p.2 < 3 := by decide

theorem rowPinsM_val (clauses : List ClauseSpec) (env : Nat) :
    ∀ p ∈ rowPinsM clauses env, p.2 < 3 := by
  intro p hp
  rw [rowPinsM_eq_palette_append] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact palettePins_val p hp
  rcases List.mem_append.mp hp with hp | hp <;>
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hp <;> simp

/-- Dropping pins keeps a spec extension, as long as the kept pins agree
    with the dropped list and every dropped pin was a legal color. -/
theorem SpecExt_of_pins_sub {E : List (MVertex × MVertex)}
    {pins₁ pins₂ : List (MVertex × Nat)} {verts : List MVertex}
    {f : MVertex → Nat} (hval : ∀ p ∈ pins₁, p.2 < 3)
    (hsub : ∀ v c, colorAt pins₂ v = some c → colorAt pins₁ v = some c)
    (hs : SpecExt E pins₁ verts [] f) : SpecExt E pins₂ verts [] f := by
  obtain ⟨hpin, hconf⟩ := hs
  refine ⟨fun v hv => ?_, hconf⟩
  have h1 := hpin v hv
  unfold pinOk at h1 ⊢
  cases h2 : colorAt pins₂ v with
  | some c =>
    show f v = c
    rw [hsub v c h2] at h1
    exact h1
  | none =>
    show f v < 3
    cases h1' : colorAt pins₁ v with
    | some cp =>
      rw [h1'] at h1
      have hfc : f v = cp := h1
      rw [hfc]
      exact hval _ (mem_of_colorAt_eq_some h1')
    | none =>
      rw [h1'] at h1
      exact h1

-- ------------------------------------------- the layer forces {T, F}

/-- In any palette-respecting proper coloring of the assembly, every
    literal-layer pair takes the colors {T, F}, one each. -/
theorem layer_forces (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) {f : MVertex → Nat}
    (hs : SpecExt (assemble threeColoring parts g clauses).2 palettePins
      (assemble threeColoring parts g clauses).1 [] f)
    {v : Nat} (hv : v < varCount clauses) :
    (f (.pos v) = 0 ∧ f (.neg v) = 1) ∨ (f (.pos v) = 1 ∧ f (.neg v) = 0) := by
  obtain ⟨hpin, hconf⟩ := hs
  -- the three layer edges of variable v are in the assembly
  have hedge : ∀ w ∈ threeColoring.layer (varCount clauses),
      normM w ∈ (assemble threeColoring parts g clauses).2 := by
    intro w hw
    exact (mem_assemble_edges threeColoring parts g clauses).mpr
      ⟨Or.inr ⟨w, hw, rfl⟩, layerM_ne _ (List.mem_map.mpr ⟨w, hw, rfl⟩)⟩
  have hadj : ∀ a b : MVertex, normM (a, b) ∈ (assemble threeColoring parts g clauses).2 →
      b ∈ adjTo (assemble threeColoring parts g clauses).2 a := by
    intro a b h
    rcases normM_swap (a, b) with hs | hs <;> rw [hs] at h
    · exact mem_adjTo.mpr (Or.inl h)
    · exact mem_adjTo.mpr (Or.inr h)
  have hlay : ∀ w, w ∈ threeColoring.layer (varCount clauses) ↔ ∃ v', v' < varCount clauses ∧
      (w = (.pos v', .neg v') ∨ w = (.pos v', .anchor 2) ∨ w = (.neg v', .anchor 2)) :=
    fun w => mem_threeColoring_layer
  have e1 := hedge (.pos v, .neg v) ((hlay _).mpr ⟨v, hv, Or.inl rfl⟩)
  have e2 := hedge (.pos v, .anchor 2) ((hlay _).mpr ⟨v, hv, Or.inr (Or.inl rfl)⟩)
  have e3 := hedge (.neg v, .anchor 2) ((hlay _).mpr ⟨v, hv, Or.inr (Or.inr rfl)⟩)
  -- vertices
  have hvp : MVertex.pos v ∈ (assemble threeColoring parts g clauses).1 :=
    (mem_assemble_verts threeColoring parts g clauses).mpr
      (Or.inl (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, List.mem_cons_self ..⟩))
  have hvn : MVertex.neg v ∈ (assemble threeColoring parts g clauses).1 :=
    (mem_assemble_verts threeColoring parts g clauses).mpr
      (Or.inl (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv,
        List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))
  have hva : MVertex.anchor 2 ∈ (assemble threeColoring parts g clauses).1 := by
    refine (mem_assemble_verts threeColoring parts g clauses).mpr (Or.inr ⟨_, e2, ?_⟩)
    rcases normM_swap (MVertex.pos v, .anchor 2) with hs | hs <;> rw [hs]
    · exact Or.inr rfl
    · exact Or.inl rfl
  -- colors are legal
  have hlt : ∀ w, w ∈ (assemble threeColoring parts g clauses).1 →
      colorAt palettePins w = none → f w < 3 := by
    intro w hw hnone
    have := hpin w hw
    unfold pinOk at this
    rw [hnone] at this
    exact this
  have hfa : f (.anchor 2) = 2 := by
    have := hpin _ hva
    unfold pinOk at this
    rw [show colorAt palettePins (.anchor 2) = some 2 by decide] at this
    exact this
  have hp3 : f (.pos v) < 3 := hlt _ hvp rfl
  have hn3 : f (.neg v) < 3 := hlt _ hvn rfl
  -- conflicts along the three edges
  have hne : ∀ a b, a ∈ (assemble threeColoring parts g clauses).1 →
      b ∈ (assemble threeColoring parts g clauses).1 →
      b ∈ adjTo (assemble threeColoring parts g clauses).2 a → f b ≠ f a := by
    intro a b ha hb hab heq
    have := hconf a ha b hab
    unfold combined at this
    rw [if_pos hb] at this
    exact this (congrArg some heq)
  have h12 := hne _ _ hvp hvn (hadj _ _ e1)
  have h13 := hne _ _ hvp hva (hadj _ _ e2)
  have h23 := hne _ _ hvn hva (hadj _ _ e3)
  omega

-- ------------------------------------------- palette ⟺ some row

/-- Palette-pinned colorability of the assembly is exactly "some row of
    the multiK table is colorable". -/
theorem colorable_assembly_iff_row (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) :
    colorable (assemble threeColoring parts g clauses).2
        (assemble threeColoring parts g clauses).1 palettePins = true
      ↔ ∃ env, env < 2 ^ varCount clauses ∧
          colorsOk (rowInstM threeColoring parts g clauses env) = true := by
  have hnd : (assemble threeColoring parts g clauses).1.Nodup := by
    show ((((List.range (varCount clauses)).flatMap fun v =>
        [MVertex.pos v, MVertex.neg v])
      ++ (assemble threeColoring parts g clauses).2.flatMap fun e =>
        [e.1, e.2]).eraseDups).Nodup
    exact nodup_eraseDups _
  have hloop : ∀ a : MVertex,
      a ∉ adjTo (assemble threeColoring parts g clauses).2 a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h <;>
      exact ((mem_assemble_edges threeColoring parts g clauses).mp h).2 rfl
  constructor
  · intro hc
    obtain ⟨f, hf⟩ := (colorable_iff_spec _ _ _ hloop hnd).mp hc
    obtain ⟨env, hlt, hbits⟩ :=
      exists_env_of_bits (fun v => decide (f (.pos v) = 0)) (varCount clauses)
    refine ⟨env, hlt, ?_⟩
    rw [colorsOk_rowInstM]
    refine (colorable_iff_spec _ _ _ hloop hnd).mpr ⟨f, ?_⟩
    obtain ⟨hpin, hconf⟩ := hf
    refine ⟨fun w hw => ?_, hconf⟩
    unfold pinOk
    cases hcw : colorAt (rowPinsM clauses env) w with
    | none =>
      show f w < 3
      have hp3 := hpin w hw
      unfold pinOk at hp3
      cases hp : colorAt palettePins w with
      | none => rw [hp] at hp3; exact hp3
      | some c =>
        have hc : colorAt (rowPinsM clauses env) w = some c := by
          rw [rowPinsM_eq_palette_append]
          exact colorAt_append_left hp
        rw [hc] at hcw
        cases hcw
    | some c =>
      show f w = c
      have hmemq := mem_of_colorAt_eq_some hcw
      rw [rowPinsM_eq_palette_append] at hmemq
      rcases List.mem_append.mp hmemq with hq | hq
      · -- an anchor: pinned identically by the palette
        have hp3 := hpin w hw
        unfold pinOk at hp3
        simp only [palettePins, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with h | h | h <;> cases h
        · rw [show colorAt palettePins (.anchor 0) = some 0 by decide] at hp3; exact hp3
        · rw [show colorAt palettePins (.anchor 1) = some 1 by decide] at hp3; exact hp3
        · rw [show colorAt palettePins (.anchor 2) = some 2 by decide] at hp3; exact hp3
      rcases List.mem_append.mp hq with hq | hq
      · -- the selected side: the pin reads the bit, the bit reads the color
        obtain ⟨x, hx, hxq⟩ := List.mem_map.mp hq
        obtain ⟨v', hv'r, rfl⟩ := List.mem_map.mp hx
        have hv' := List.mem_range.mp hv'r
        have hforce := layer_forces parts g clauses ⟨hpin, hconf⟩ hv'
        have hb : (env >>> v' &&& 1 == 1) = decide (f (.pos v') = 0) := by
          rw [bit_eq_testBit]
          exact hbits v' hv'
        by_cases h0 : f (.pos v') = 0
        · rw [if_pos (by rw [hb]; simp [h0])] at hxq
          cases hxq
          exact h0
        · rw [if_neg (by rw [hb]; simp [h0])] at hxq
          cases hxq
          rcases hforce with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h h0
          · exact h
      · -- the forbidden side
        obtain ⟨x, hx, hxq⟩ := List.mem_map.mp hq
        obtain ⟨v', hv'r, rfl⟩ := List.mem_map.mp hx
        have hv' := List.mem_range.mp hv'r
        have hforce := layer_forces parts g clauses ⟨hpin, hconf⟩ hv'
        have hb : (env >>> v' &&& 1 == 1) = decide (f (.pos v') = 0) := by
          rw [bit_eq_testBit]
          exact hbits v' hv'
        by_cases h0 : f (.pos v') = 0
        · rw [if_pos (by rw [hb]; simp [h0])] at hxq
          cases hxq
          rcases hforce with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · omega
        · rw [if_neg (by rw [hb]; simp [h0])] at hxq
          cases hxq
          rcases hforce with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h h0
          · exact h
  · rintro ⟨env, _, hrow⟩
    rw [colorsOk_rowInstM] at hrow
    obtain ⟨f, hf⟩ := (colorable_iff_spec _ _ _ hloop hnd).mp hrow
    refine (colorable_iff_spec _ _ _ hloop hnd).mpr ⟨f, ?_⟩
    refine SpecExt_of_pins_sub (rowPinsM_val clauses env) (fun v c h => ?_) hf
    rw [rowPinsM_eq_palette_append]
    exact colorAt_append_left h

/-- The reduction, pin-free: for any local gadget passing the raw
    eight-row table and any well-formed formula, the assembly is
    3-colorable with its palette pinned iff the formula is satisfiable. -/
theorem colorable_assembly_iff_sat (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hgk : gadgetK threeColoring parts g false = some 1)
    {clauses : List ClauseSpec} (hwf : WfClauses clauses) :
    colorable (assemble threeColoring parts g clauses).2
        (assemble threeColoring parts g clauses).1 palettePins = true
      ↔ ∃ env, env < 2 ^ varCount clauses ∧ formulaSat env clauses = true := by
  rw [colorable_assembly_iff_row]
  constructor <;> rintro ⟨env, hlt, h⟩ <;> refine ⟨env, hlt, ?_⟩
  · rwa [colorsOk_rowInstM_eq parts hsub hgk hwf] at h
  · rwa [colorsOk_rowInstM_eq parts hsub hgk hwf]

/-- The textbook statement on the sweep's own find: the trident assembly
    (palette pinned) is 3-colorable iff the formula is satisfiable. -/
theorem trident_colorable_iff {clauses : List ClauseSpec}
    (hwf : WfClauses clauses) :
    colorable (assemble threeColoring [3, 3] tridentA clauses).2
        (assemble threeColoring [3, 3] tridentA clauses).1 palettePins = true
      ↔ ∃ env, env < 2 ^ varCount clauses ∧ formulaSat env clauses = true :=
  colorable_assembly_iff_sat [3, 3] tridentA_sub tridentA_gadgetK_raw hwf

end Atlas
