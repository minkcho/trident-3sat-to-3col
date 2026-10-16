import atlas.ProofsSym
/-!
  P6-2 (glue half): the 3-coloring verifier factorizes over unions of
  edge lists whose parts pairwise share only pinned vertices.

  All statements are at the `SpecExt` level of ProofsColor and generic
  in the vertex type; the layer of a multi-clause row is just another
  part (all its endpoints are pinned), so no special treatment for it
  exists here -- its own conjunct is discharged by
  `colorable_of_pinned_edges`. Also: the membership-restricted variants
  of the pin/vertex congruences that the copy-transfer step needs
  (`colorable_congr_pins_mem`, `colorable_congr_verts_touched`).
-/

namespace Atlas

open List

variable {α : Type} [BEq α] [LawfulBEq α]

/-- `v` is an endpoint of some edge of `E`. -/
def touches (E : List (α × α)) (v : α) : Prop :=
  ∃ u, u ∈ adjTo E v

omit [LawfulBEq α] in
theorem adjTo_append (E₁ E₂ : List (α × α)) (v : α) :
    adjTo (E₁ ++ E₂) v = adjTo E₁ v ++ adjTo E₂ v :=
  List.filterMap_append ..

omit [LawfulBEq α] in
theorem adjTo_flatten_mem {Es : List (List (α × α))} {v u : α} :
    u ∈ adjTo Es.flatten v ↔ ∃ E ∈ Es, u ∈ adjTo E v := by
  induction Es with
  | nil =>
    constructor
    · intro h
      cases h
    · rintro ⟨E, hE, _⟩
      cases hE
  | cons E rest ih =>
    rw [List.flatten_cons, adjTo_append, List.mem_append, ih]
    constructor
    · rintro (h | ⟨E', hE', h⟩)
      · exact ⟨E, List.mem_cons_self .., h⟩
      · exact ⟨E', List.mem_cons_of_mem _ hE', h⟩
    · rintro ⟨E', hE', h⟩
      rcases List.mem_cons.mp hE' with rfl | hE''
      · exact Or.inl h
      · exact Or.inr ⟨E', hE'', h⟩

omit [LawfulBEq α] in
theorem touches_flatten {Es : List (List (α × α))} {v : α} :
    touches Es.flatten v ↔ ∃ E ∈ Es, touches E v := by
  unfold touches
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨E, hE, h⟩ := adjTo_flatten_mem.mp hu
    exact ⟨E, hE, u, h⟩
  · rintro ⟨E, hE, u, hu⟩
    exact ⟨u, adjTo_flatten_mem.mpr ⟨E, hE, hu⟩⟩

-- ------------------------------------ membership-restricted congruences

theorem SpecExt_congr_pins_mem {edges : List (α × α)}
    {pins₁ pins₂ : List (α × Nat)} {verts : List α}
    (h : ∀ u ∈ verts, colorAt pins₁ u = colorAt pins₂ u) {f : α → Nat}
    (hs : SpecExt edges pins₁ verts [] f) :
    SpecExt edges pins₂ verts [] f := by
  obtain ⟨hpin, hconf⟩ := hs
  refine ⟨fun v hv => ?_, hconf⟩
  have hp := hpin v hv
  unfold pinOk at hp ⊢
  rw [← h v hv]
  exact hp

theorem colorable_congr_pins_mem (edges : List (α × α)) (verts : List α)
    {pins₁ pins₂ : List (α × Nat)} (hloop : ∀ a : α, a ∉ adjTo edges a)
    (hnd : verts.Nodup)
    (h : ∀ u ∈ verts, colorAt pins₁ u = colorAt pins₂ u) :
    colorable edges verts pins₁ = colorable edges verts pins₂ := by
  have h1 := colorable_iff_spec edges verts pins₁ hloop hnd
  have h2 := colorable_iff_spec edges verts pins₂ hloop hnd
  cases hc : colorable edges verts pins₂
  · cases hc1 : colorable edges verts pins₁
    · rfl
    · obtain ⟨f, hf⟩ := h1.mp hc1
      have := h2.mpr ⟨f, SpecExt_congr_pins_mem h hf⟩
      rw [hc] at this
      cases this
  · obtain ⟨f, hf⟩ := h2.mp hc
    exact h1.mpr ⟨f, SpecExt_congr_pins_mem (fun u hu => (h u hu).symm) hf⟩

theorem colorable_congr_verts_touched (edges : List (α × α))
    (pins : List (α × Nat)) {verts₁ verts₂ : List α}
    (hloop : ∀ a : α, a ∉ adjTo edges a) (hnd₁ : verts₁.Nodup)
    (hnd₂ : verts₂.Nodup)
    (h : ∀ u : α, touches edges u → (u ∈ verts₁ ↔ u ∈ verts₂)) :
    colorable edges verts₁ pins = colorable edges verts₂ pins := by
  classical
  have transfer : ∀ {va vb : List α},
      (∀ u : α, touches edges u → (u ∈ va ↔ u ∈ vb)) →
      (∃ f, SpecExt edges pins va [] f) →
      ∃ f, SpecExt edges pins vb [] f := by
    intro va vb hab ⟨f, hpin, hconf⟩
    refine ⟨fun u => if u ∈ va then f u else (colorAt pins u).getD 0, ?_, ?_⟩
    · intro v hv
      by_cases hva : v ∈ va
      · have hp := hpin v hva
        unfold pinOk at hp ⊢
        simp only [if_pos hva]
        exact hp
      · unfold pinOk
        simp only [if_neg hva]
        cases hcv : colorAt pins v
        · simp
        · simp
    · intro v hv u hu
      have htv : touches edges v := ⟨u, hu⟩
      have htu : touches edges u := ⟨v, adjTo_symm hu⟩
      have hva : v ∈ va := (hab v htv).mpr hv
      have hcf := hconf v hva u hu
      unfold combined at hcf ⊢
      by_cases hub : u ∈ vb
      · have hua : u ∈ va := (hab u htu).mpr hub
        rw [if_pos hua] at hcf
        simp only [if_pos hub, if_pos hua, if_pos hva]
        exact hcf
      · have hua : u ∉ va := fun hc => hub ((hab u htu).mp hc)
        rw [if_neg hua] at hcf
        simp only [if_neg hub, if_pos hva]
        exact hcf
  have h1 := colorable_iff_spec edges verts₁ pins hloop hnd₁
  have h2 := colorable_iff_spec edges verts₂ pins hloop hnd₂
  cases hc : colorable edges verts₂ pins
  · cases hc1 : colorable edges verts₁ pins
    · rfl
    · have := h2.mpr (transfer h (h1.mp hc1))
      rw [hc] at this
      cases this
  · exact h1.mpr (transfer (fun u hu => (h u hu).symm) (h2.mp hc))

-- ----------------------------------------------- fully pinned edge lists

/-- An edge list whose endpoints are all pinned to distinct colors is
    colorable outright: the pins themselves are the witness. -/
theorem colorable_of_pinned_edges (E : List (α × α)) (verts : List α)
    (pins : List (α × Nat)) (hloop : ∀ a : α, a ∉ adjTo E a)
    (hnd : verts.Nodup)
    (hpin : ∀ e ∈ E, ∃ c₁ c₂, colorAt pins e.1 = some c₁ ∧
      colorAt pins e.2 = some c₂ ∧ c₁ ≠ c₂) :
    colorable E verts pins = true := by
  refine (colorable_iff_spec E verts pins hloop hnd).mpr
    ⟨fun v => (colorAt pins v).getD 0, ?_, ?_⟩
  · intro v _
    unfold pinOk
    cases hcv : colorAt pins v
    · simp [hcv]
    · simp [hcv]
  · intro v hv u hu
    unfold combined
    rcases mem_adjTo.mp hu with hE | hE
    · obtain ⟨c₁, c₂, hp1, hp2, hne⟩ := hpin (v, u) hE
      by_cases hum : u ∈ verts
      · simp only [if_pos hum, hp1, hp2, Option.getD_some]
        exact fun hcon => hne (Option.some.inj hcon).symm
      · rw [if_neg hum, colorAt_nil]
        exact fun hcon => nomatch hcon
    · obtain ⟨c₁, c₂, hp1, hp2, hne⟩ := hpin (u, v) hE
      by_cases hum : u ∈ verts
      · simp only [if_pos hum, hp1, hp2, Option.getD_some]
        exact fun hcon => hne (Option.some.inj hcon)
      · rw [if_neg hum, colorAt_nil]
        exact fun hcon => nomatch hcon

-- --------------------------------------------------------------- gluing

theorem SpecExt_restrict {E₁ E₂ : List (α × α)} {pins : List (α × Nat)}
    {verts : List α} {f : α → Nat}
    (hs : SpecExt (E₁ ++ E₂) pins verts [] f) :
    SpecExt E₁ pins verts [] f ∧ SpecExt E₂ pins verts [] f := by
  obtain ⟨hpin, hconf⟩ := hs
  constructor
  · refine ⟨hpin, fun v hv u hu => hconf v hv u ?_⟩
    rw [adjTo_append, List.mem_append]
    exact Or.inl hu
  · refine ⟨hpin, fun v hv u hu => hconf v hv u ?_⟩
    rw [adjTo_append, List.mem_append]
    exact Or.inr hu

/-- The binary glue: if every vertex touching both parts is pinned, the
    union is colorable exactly when both parts are. -/
theorem colorable_glue_two (E₁ E₂ : List (α × α)) (verts : List α)
    (pins : List (α × Nat)) (hloop₁ : ∀ a : α, a ∉ adjTo E₁ a)
    (hloop₂ : ∀ a : α, a ∉ adjTo E₂ a) (hnd : verts.Nodup)
    (hshared : ∀ v : α, touches E₁ v → touches E₂ v →
      (colorAt pins v).isSome = true) :
    colorable (E₁ ++ E₂) verts pins
      = (colorable E₁ verts pins && colorable E₂ verts pins) := by
  classical
  have hloop : ∀ a : α, a ∉ adjTo (E₁ ++ E₂) a := by
    intro a ha
    rw [adjTo_append] at ha
    rcases List.mem_append.mp ha with h | h
    · exact hloop₁ a h
    · exact hloop₂ a h
  have h12 := colorable_iff_spec (E₁ ++ E₂) verts pins hloop hnd
  have h1 := colorable_iff_spec E₁ verts pins hloop₁ hnd
  have h2 := colorable_iff_spec E₂ verts pins hloop₂ hnd
  cases hc1 : colorable E₁ verts pins
  · rw [Bool.false_and]
    cases hc12 : colorable (E₁ ++ E₂) verts pins
    · rfl
    · obtain ⟨f, hf⟩ := h12.mp hc12
      have := h1.mpr ⟨f, (SpecExt_restrict hf).1⟩
      rw [hc1] at this
      cases this
  · cases hc2 : colorable E₂ verts pins
    · rw [Bool.and_false]
      cases hc12 : colorable (E₁ ++ E₂) verts pins
      · rfl
      · obtain ⟨f, hf⟩ := h12.mp hc12
        have := h2.mpr ⟨f, (SpecExt_restrict hf).2⟩
        rw [hc2] at this
        cases this
    · rw [Bool.and_true]
      obtain ⟨f₁, hf₁⟩ := h1.mp hc1
      obtain ⟨f₂, hf₂⟩ := h2.mp hc2
      -- on doubly-touched vertices of `verts` the two witnesses agree
      -- with the pin, hence with each other
      have hagree : ∀ w ∈ verts, touches E₁ w → touches E₂ w →
          f₁ w = f₂ w := by
        intro w hw ht1 ht2
        have hs := hshared w ht1 ht2
        cases hcw : colorAt pins w with
        | none =>
          rw [hcw] at hs
          cases hs
        | some cp =>
          have hp1 := hf₁.1 w hw
          have hp2 := hf₂.1 w hw
          unfold pinOk at hp1 hp2
          rw [hcw] at hp1 hp2
          rw [hp1, hp2]
      refine h12.mpr ⟨fun u => if touches E₁ u then f₁ u else f₂ u, ?_, ?_⟩
      · intro v hv
        by_cases ht : touches E₁ v
        · have hp := hf₁.1 v hv
          unfold pinOk at hp ⊢
          simp only [if_pos ht]
          exact hp
        · have hp := hf₂.1 v hv
          unfold pinOk at hp ⊢
          simp only [if_neg ht]
          exact hp
      · intro v hv u hu
        rw [adjTo_append, List.mem_append] at hu
        rcases hu with hu₁ | hu₂
        · have htv : touches E₁ v := ⟨u, hu₁⟩
          have htu : touches E₁ u := ⟨v, adjTo_symm hu₁⟩
          have hcf := hf₁.2 v hv u hu₁
          unfold combined at hcf ⊢
          by_cases hum : u ∈ verts
          · rw [if_pos hum] at hcf
            simp only [if_pos hum, if_pos htv, if_pos htu]
            exact hcf
          · rw [if_neg hum] at hcf
            simp only [if_neg hum, if_pos htv]
            exact hcf
        · have htv2 : touches E₂ v := ⟨u, hu₂⟩
          have htu2 : touches E₂ u := ⟨v, adjTo_symm hu₂⟩
          have hcf := hf₂.2 v hv u hu₂
          unfold combined at hcf ⊢
          have hfv : (if touches E₁ v then f₁ v else f₂ v) = f₂ v := by
            by_cases htv1 : touches E₁ v
            · rw [if_pos htv1]
              exact hagree v hv htv1 htv2
            · rw [if_neg htv1]
          by_cases hum : u ∈ verts
          · have hfu : (if touches E₁ u then f₁ u else f₂ u) = f₂ u := by
              by_cases htu1 : touches E₁ u
              · rw [if_pos htu1]
                exact hagree u hum htu1 htu2
              · rw [if_neg htu1]
            rw [if_pos hum] at hcf
            simp only [if_pos hum, hfv, hfu]
            exact hcf
          · rw [if_neg hum] at hcf
            simp only [if_neg hum, hfv]
            exact hcf

/-- Normalization that at most swaps an edge's endpoints never changes
    adjacency (generic form of `adjTo_map_normEdge`). -/
theorem adjTo_map_swap {nf : α × α → α × α}
    (hswap : ∀ e : α × α, nf e = e ∨ nf e = (e.2, e.1))
    (l : List (α × α)) (v u : α) :
    u ∈ adjTo (l.map nf) v ↔ u ∈ adjTo l v := by
  rw [mem_adjTo, mem_adjTo]
  have mem_of : ∀ {a b : α}, (a, b) ∈ l.map nf → (a, b) ∈ l ∨ (b, a) ∈ l := by
    intro a b h
    obtain ⟨e, he, heq⟩ := List.mem_map.mp h
    rcases hswap e with hs | hs
    · rw [hs] at heq
      exact Or.inl (heq ▸ he)
    · rw [hs] at heq
      have h1 : e.2 = a := congrArg Prod.fst heq
      have h2 : e.1 = b := congrArg Prod.snd heq
      rw [← h1, ← h2]
      exact Or.inr he
  have push : ∀ {a b : α}, (a, b) ∈ l →
      ((a, b) ∈ l.map nf ∨ (b, a) ∈ l.map nf) := by
    intro a b hab
    have hm : nf (a, b) ∈ l.map nf := List.mem_map.mpr ⟨(a, b), hab, rfl⟩
    rcases hswap (a, b) with hs | hs
    · rw [hs] at hm
      exact Or.inl hm
    · rw [hs] at hm
      exact Or.inr hm
  constructor
  · rintro (h | h)
    · rcases mem_of h with h' | h'
      exacts [Or.inl h', Or.inr h']
    · rcases mem_of h with h' | h'
      exacts [Or.inr h', Or.inl h']
  · rintro (h | h)
    · rcases push h with h' | h'
      exacts [Or.inl h', Or.inr h']
    · rcases push h with h' | h'
      exacts [Or.inr h', Or.inl h']

/-- The n-ary glue: over pairwise pin-separated parts the verifier is
    the conjunction of the per-part verifiers. -/
theorem colorable_glue (parts : List (List (α × α))) (verts : List α)
    (pins : List (α × Nat))
    (hloop : ∀ E ∈ parts, ∀ a : α, a ∉ adjTo E a) (hnd : verts.Nodup)
    (hshared : parts.Pairwise fun E E' => ∀ v : α,
      touches E v → touches E' v → (colorAt pins v).isSome = true) :
    colorable parts.flatten verts pins
      = parts.all fun E => colorable E verts pins := by
  induction parts with
  | nil =>
    show colorable [] verts pins = true
    exact colorable_of_pinned_edges [] verts pins
      (fun a ha => by cases ha) hnd (fun e he => by cases he)
  | cons E rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hshared
    have hloopE := hloop E (List.mem_cons_self ..)
    have hloopRest : ∀ a : α, a ∉ adjTo rest.flatten a := by
      intro a ha
      obtain ⟨E', hE', h⟩ := adjTo_flatten_mem.mp ha
      exact hloop E' (List.mem_cons_of_mem _ hE') a h
    rw [List.flatten_cons,
      colorable_glue_two E rest.flatten verts pins hloopE hloopRest hnd ?_,
      ih (fun E' hE' => hloop E' (List.mem_cons_of_mem _ hE')) htail,
      List.all_cons]
    intro v ht1 ht2
    obtain ⟨E', hE', ht'⟩ := touches_flatten.mp ht2
    exact hhead E' hE' v ht1 ht'

end Atlas
