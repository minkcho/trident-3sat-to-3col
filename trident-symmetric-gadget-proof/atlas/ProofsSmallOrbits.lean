import atlas.ProofsSym
import atlas.ProofsOrbit

/-!
  Orbit compositions of sizes 1 and 2 only carry no valid clause gadget, for
  any number of auxiliary vertices. This is the special case of the paper's
  degree-one channel lemma (Lemma 11) that its minimality proof uses.

  Every auxiliary vertex of an orbit of size 1 or 2, and every palette anchor,
  is fixed by the even permutation `cyc` (x0 ↦ x1 ↦ x2 ↦ x0). By S3-invariance,
  every neighbor of x2 is therefore also a neighbor of x0. Take a proper
  coloring under the satisfying input (F, F, T) and recolor x2 with F. Each
  neighbor of x2 still avoids F, because it is adjacent to x0, which is
  colored F. The result is a proper coloring under (F, F, F), so the gadget
  accepts the unsatisfying input and is not valid.
-/

namespace Atlas

open List

/-- The even permutation with `app cyc 2 = 0`. -/
def cyc : Perm := (1, 2, 0)

theorem cyc_mem : cyc ∈ perms := by decide

theorem cyc_parity : parity cyc = 0 := by decide

/-- In a universe whose parts all have size 1 or 2, `cyc` fixes every
    auxiliary vertex. -/
theorem act_cyc_aux {U : Universe} {p j : Nat}
    (h : U.size p = 1 ∨ U.size p = 2) : U.act cyc (.aux p j) = .aux p j := by
  rcases h with h | h
  · exact act_aux_one cyc j h
  · rw [act_aux_two cyc j h, cyc_parity, Nat.xor_zero]

/-- The parts of the 3-coloring universe over orbit sizes 1 and 2, with the
    three appended anchor parts, all have size 1 or 2. -/
theorem attach_size_small (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2) {p : Nat}
    (hp : p < (threeColoring.attach parts).1.parts.length) :
    (threeColoring.attach parts).1.size p = 1 ∨
      (threeColoring.attach parts).1.size p = 2 := by
  rw [attach_parts, List.length_append] at hp
  by_cases hlt : p < parts.length
  · have hget : (threeColoring.attach parts).1.size p = parts[p] := by
      show (parts ++ [1, 1, 1]).getD p 0 = parts[p]
      rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
    rw [hget]
    exact hparts _ (List.getElem_mem hlt)
  · left
    obtain ⟨d, rfl⟩ : ∃ d, p = parts.length + d := ⟨p - parts.length, by omega⟩
    have hd : d < 3 := by simp at hp; omega
    exact attach_size parts hd

/-- `normEdge` keeps the pair or swaps it. -/
theorem normEdge_cases (a b : Vertex) :
    normEdge (a, b) = (a, b) ∨ normEdge (a, b) = (b, a) := by
  unfold normEdge
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Over orbit sizes 1 and 2, every neighbor of x2 in an S3-invariant graph
    is a neighbor of x0. -/
theorem adj_lit_two_to_zero (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2) {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ s ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge s e ∈ g)
    {w : Vertex} (hw : w ∈ adjTo g (.lit 2)) : w ∈ adjTo g (.lit 0) := by
  have hll : (threeColoring.attach parts).1.litLit = false := rfl
  -- the neighbor is an auxiliary vertex of an orbit of size 1 or 2
  have hfix : ∀ e ∈ g, (e.1 = .lit 2 ∧ e.2 = w) ∨ (e.1 = w ∧ e.2 = .lit 2) →
      (threeColoring.attach parts).1.act cyc w = w := by
    intro e he hends
    have hwv : w ∈ (threeColoring.attach parts).1.vertices := by
      rcases hends with ⟨_, h⟩ | ⟨h, _⟩
      · exact h ▸ (mem_edges (hg e he)).2.1
      · exact h ▸ (mem_edges (hg e he)).1
    rcases mem_vertices.mp hwv with ⟨i, _, rfl⟩ | ⟨p, j, hp, _, rfl⟩
    · exfalso
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact lit_pair_not_mem hll (hg e he) h1 h2
      · exact lit_pair_not_mem hll (hg e he) h1 h2
    · exact act_cyc_aux (attach_size_small parts hparts hp)
  rcases mem_adjTo.mp hw with h | h
  · have hw' := hfix _ h (Or.inl ⟨rfl, rfl⟩)
    have himg := hinv cyc cyc_mem _ h
    have hact : (threeColoring.attach parts).1.actEdge cyc (.lit 2, w)
        = normEdge (.lit 0, w) := by
      show normEdge ((threeColoring.attach parts).1.act cyc (.lit 2),
        (threeColoring.attach parts).1.act cyc w) = normEdge (.lit 0, w)
      rw [hw']
      rfl
    rw [hact] at himg
    rcases normEdge_cases (.lit 0) w with hn | hn <;> rw [hn] at himg
    · exact mem_adjTo.mpr (Or.inl himg)
    · exact mem_adjTo.mpr (Or.inr himg)
  · have hw' := hfix _ h (Or.inr ⟨rfl, rfl⟩)
    have himg := hinv cyc cyc_mem _ h
    have hact : (threeColoring.attach parts).1.actEdge cyc (w, .lit 2)
        = normEdge (w, .lit 0) := by
      show normEdge ((threeColoring.attach parts).1.act cyc w,
        (threeColoring.attach parts).1.act cyc (.lit 2)) = normEdge (w, .lit 0)
      rw [hw']
      rfl
    rw [hact] at himg
    rcases normEdge_cases w (.lit 0) with hn | hn <;> rw [hn] at himg
    · exact mem_adjTo.mpr (Or.inr himg)
    · exact mem_adjTo.mpr (Or.inl himg)

theorem rowPins_four (parts : List Nat) :
    rowPins parts 4 =
      [(Vertex.aux parts.length 0, 0), (.aux (parts.length + 1) 0, 1),
       (.aux (parts.length + 2) 0, 2), (.lit 2, 0), (.lit 0, 1), (.lit 1, 1)] := by
  rw [rowPins_eq]
  rfl

theorem rowPins_zero (parts : List Nat) :
    rowPins parts 0 =
      [(Vertex.aux parts.length 0, 0), (.aux (parts.length + 1) 0, 1),
       (.aux (parts.length + 2) 0, 2), (.lit 0, 1), (.lit 1, 1), (.lit 2, 1)] := by
  rw [rowPins_eq]
  rfl

/-- The two pin lists agree everywhere except at x2. -/
theorem colorAt_rowPins_zero_four (parts : List Nat) {v : Vertex}
    (hv : v ≠ .lit 2) :
    colorAt (rowPins parts 0) v = colorAt (rowPins parts 4) v := by
  rw [rowPins_zero, rowPins_four]
  cases v with
  | lit i =>
    have hi : ¬(2 = i) := fun h => hv (by rw [h])
    simp only [colorAt_cons, colorAt_nil]
    by_cases h0 : 0 = i
    · subst h0
      simp
    · by_cases h1 : 1 = i
      · subst h1
        simp
      · simp [h0, h1, hi]
  | aux p j =>
    simp only [colorAt_cons, colorAt_nil]
    simp

/-- Over orbit sizes 1 and 2: if a gadget accepts (F, F, T) it accepts
    (F, F, F). -/
theorem colorsOk_row_four_imp_zero (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2) {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ s ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge s e ∈ g)
    (h4 : colorsOk (rowInst parts g 4) = true) :
    colorsOk (rowInst parts g 0) = true := by
  have hne : ∀ e ∈ g, e.1 ≠ e.2 := fun e he => edges_ne (hg e he)
  have hloopg : ∀ a : Vertex, a ∉ adjTo g a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h
    · exact hne (a, a) h rfl
    · exact hne (a, a) h rfl
  have hnd := vertices_nodup (threeColoring.attach parts).1
  change colorable g (threeColoring.attach parts).1.vertices
    (rowPins parts 4) = true at h4
  show colorable g (threeColoring.attach parts).1.vertices
    (rowPins parts 0) = true
  obtain ⟨f, hpin, hconf⟩ :=
    (colorable_iff_spec g _ (rowPins parts 4) hloopg hnd).mp h4
  have hlit0 : Vertex.lit 0 ∈ (threeColoring.attach parts).1.vertices :=
    mem_vertices.mpr (Or.inl ⟨0, by decide, rfl⟩)
  have hf0 : f (.lit 0) = 1 := by
    have := hpin _ hlit0
    unfold pinOk at this
    rw [rowPins_four] at this
    simpa [colorAt_cons, colorAt_nil] using this
  -- recolor x2 with F
  let f' : Vertex → Nat := fun v => if v = .lit 2 then 1 else f v
  refine (colorable_iff_spec g _ (rowPins parts 0) hloopg hnd).mpr ⟨f', ?_, ?_⟩
  · intro v hv
    by_cases h2 : v = .lit 2
    · subst h2
      unfold pinOk
      rw [rowPins_zero]
      simp [f', colorAt_cons]
    · have := hpin v hv
      unfold pinOk at this ⊢
      rw [colorAt_rowPins_zero_four parts h2]
      simpa [f', h2] using this
  · intro v hv u hu
    unfold combined
    split
    · rename_i huv
      intro heq
      have heq' := Option.some.inj heq
      by_cases hv2 : v = .lit 2
      · subst hv2
        have hu2 : u ≠ .lit 2 := fun h => hloopg _ (h ▸ hu)
        have hu0 := adj_lit_two_to_zero parts hparts hg hinv hu
        have hc := hconf _ hlit0 u hu0
        unfold combined at hc
        rw [if_pos huv, hf0] at hc
        simp only [f', hu2, if_false, if_true] at heq'
        exact hc (by rw [heq'])
      · by_cases hu2 : u = .lit 2
        · subst hu2
          have hv' : v ∈ adjTo g (.lit 2) := by
            rcases mem_adjTo.mp hu with h | h
            · exact mem_adjTo.mpr (Or.inr h)
            · exact mem_adjTo.mpr (Or.inl h)
          have hv0 := adj_lit_two_to_zero parts hparts hg hinv hv'
          have hc := hconf _ hlit0 v hv0
          unfold combined at hc
          rw [if_pos hv, hf0] at hc
          simp only [f', hv2, if_false, if_true] at heq'
          exact hc (by rw [← heq'])
        · have hc := hconf v hv u hu
          unfold combined at hc
          rw [if_pos huv] at hc
          simp only [f', hu2, hv2, if_false] at heq'
          exact hc (by rw [heq'])
    · simp [colorAt_nil]

/-- Orbit compositions of sizes 1 and 2 only carry no valid clause gadget:
    every S3-invariant graph of such a slice is rejected by the raw
    eight-row table, at any number of auxiliary vertices. -/
theorem gadgetK_none_of_small_orbits (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2) {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hinv : ∀ s ∈ perms, ∀ e ∈ g,
      (threeColoring.attach parts).1.actEdge s e ∈ g) :
    gadgetK threeColoring parts g false = none := by
  cases hk : gadgetK threeColoring parts g false with
  | none => rfl
  | some b =>
    exfalso
    rw [gadgetK_eq threeColoring parts g false rfl, checkGadget_rows_eqP] at hk
    obtain ⟨_, hall⟩ := (commonK_eq_some_iff threeColoring).mp hk
    -- the faithful column of each row: exact = (budget is 1 and colorable)
    have hex : ∀ r ∈ (List.range 8).map (fun env =>
        (env != 0, rowInstP threeColoring parts g env)),
        (threeColoring.exact r.2 b == r.1) = true := by
      intro r hr
      have h := hall r hr
      unfold rowCond at h
      exact ((Bool.and_eq_true _ _).mp h).2
    have e4 := hex _ (List.mem_map.mpr ⟨4, List.mem_range.mpr (by decide), rfl⟩)
    have e0 := hex _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by decide), rfl⟩)
    change ((b == 1 && colorsOk (rowInst parts g 4)) == true) = true at e4
    change ((b == 1 && colorsOk (rowInst parts g 0)) == false) = true at e0
    have hb4 : (b == 1 && colorsOk (rowInst parts g 4)) = true := by
      simpa using e4
    obtain ⟨hb, h4⟩ := (Bool.and_eq_true _ _).mp hb4
    have h0 := colorsOk_row_four_imp_zero parts hparts hg hinv h4
    rw [hb, h0] at e0
    exact absurd e0 (by decide)

end Atlas
