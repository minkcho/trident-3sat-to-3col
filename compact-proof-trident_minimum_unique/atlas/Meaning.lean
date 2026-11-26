import atlas.ProofsOrbit
import atlas.Proofs
import atlas.ProofsSym

/-!
  What the statements mean. `Statement.lean` speaks about engine functions:
  `compositions`, the universe built by `threeColoring.attach`, its action
  `Universe.act`, and the judge `gadgetK`. The theorems below say, in plain
  terms, what each of these is, so that a reader can check the statements
  without reading the engine.

  1. `mem_compositions_iff`: `compositions k [1, 2, 3, 6]` lists exactly the
     non-decreasing lists over {1, 2, 3, 6} summing to k. Nothing is missing,
     so "for every composition in the list" means "for every orbit
     composition".
  2. `attach_action`: on every candidate universe, `Universe.act` is an
     action of S3: the identity acts trivially, it is compatible with
     composition, it maps the vertex list onto itself, it permutes the
     literals naturally, and it fixes the three palette anchors. With
     `attach_mulAction` it is a mathlib `MulAction` of the group `S3`, and
     every edge orbit has size 1, 2, 3 or 6 (`attach_edgeOrbit_length`).
  3. `gadgetK_some_iff`: `gadgetK threeColoring parts g false = some b`
     holds exactly when b = 1 and, for each of the eight inputs, the row is
     3-colorable iff the input satisfies the clause (`env ≠ 0`).
     `colorsOk_rowInst_iff` says what "the row is 3-colorable" means: a
     choice of colors 0, 1, 2 for every vertex that respects the pins (the
     anchors T, F, B; the true literals T; the false literals F) and gives
     adjacent vertices different colors.

  Not formalized: that every S3-symmetric gadget of Definition 1 can be
  relabeled into a candidate of this space (the paper's Lemma 6, with the
  standard classification of transitive S3-sets).
-/

namespace Atlas.Meaning

open Atlas

-- ------------------------------------------------------------ 1. compositions

theorem mem_compositions_iff {k : Nat} {c : List Nat} :
    c ∈ compositions k [1, 2, 3, 6] ↔
      c.sum = k ∧ (∀ x ∈ c, x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 6) ∧ c.Pairwise (· ≤ ·) := by
  have hls : legalSizes [1, 2, 3, 6] = [1, 2, 3, 6] := rfl
  constructor
  · intro h
    obtain ⟨hs, hm, hp⟩ := compositions_sound h
    refine ⟨hs, fun x hx => ?_, hp⟩
    have := hm x hx
    rw [hls] at this
    simpa using this
  · rintro ⟨hs, hm, hp⟩
    refine compositions_complete hs (fun x hx => ?_) hp
    rw [hls]
    rcases hm x hx with h | h | h | h <;> simp [h]

-- ------------------------------------------------------------------ 2. action

theorem attach_action (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) :
    (∀ v ∈ (threeColoring.attach parts).1.vertices,
        (threeColoring.attach parts).1.act (0, 1, 2) v = v) ∧
    (∀ s ∈ perms, ∀ t ∈ perms, ∀ v,
        (threeColoring.attach parts).1.act s ((threeColoring.attach parts).1.act t v)
          = (threeColoring.attach parts).1.act (compose s t) v) ∧
    (∀ s ∈ perms, ∀ v ∈ (threeColoring.attach parts).1.vertices,
        (threeColoring.attach parts).1.act s v ∈ (threeColoring.attach parts).1.vertices) ∧
    (∀ s ∈ perms, ∀ i, (threeColoring.attach parts).1.act s (.lit i) = .lit (app s i)) ∧
    (∀ s ∈ perms, ∀ a ∈ anchorsOf parts.length (threeColoring.attach parts).1,
        (threeColoring.attach parts).1.act s a = a) := by
  have hU := attach_legal parts hparts
  refine ⟨fun v hv => act_id hU hv, fun s hs t ht v => act_compose _ hs ht v,
    fun s hs v hv => act_mem hU hs hv, fun s _ i => rfl, ?_⟩
  intro s _ a ha
  rw [attach_anchors] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact act_aux_one s 0 (by simpa using attach_size parts (d := 0) (by decide))
  · exact act_aux_one s 0 (attach_size parts (d := 1) (by decide))
  · exact act_aux_one s 0 (attach_size parts (d := 2) (by decide))

/-- The action is a mathlib group action of `S3` on the vertices. -/
theorem attach_mulAction (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) :
    Nonempty (MulAction S3
      (LegalUniverse.Vert ⟨(threeColoring.attach parts).1, attach_legal parts hparts⟩)) :=
  ⟨inferInstance⟩

/-- Every edge orbit of a candidate universe has size 1, 2, 3 or 6. -/
theorem attach_edgeOrbit_length (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) {e : Edge}
    (he : e ∈ (threeColoring.attach parts).1.edges) :
    ((threeColoring.attach parts).1.edgeOrbit e).length ∈ [1, 2, 3, 6] :=
  edgeOrbit_length_legal (attach_legal parts hparts) he

-- ------------------------------------------------------------- 3. the judge

theorem gadgetK_some_iff (parts : List Nat) (g : List Edge) (b : Nat) :
    gadgetK threeColoring parts g false = some b ↔
      b = 1 ∧ ∀ env, env < 8 → (colorsOk (rowInst parts g env) = true ↔ env ≠ 0) := by
  rw [gadgetK_eq threeColoring parts g false rfl, checkGadget_rows_eqP,
    commonK_eq_some_iff]
  have hmem : ∀ env, env < 8 → ((env != 0), rowInstP threeColoring parts g env) ∈
      (gadgetEnvs false).map (fun env => ((env != 0), rowInstP threeColoring parts g env)) :=
    fun env henv => List.mem_map.mpr ⟨env, by simpa [gadgetEnvs] using henv, rfl⟩
  constructor
  · rintro ⟨_, hall⟩
    have hcond : ∀ env, env < 8 →
        rowCond threeColoring b ((env != 0), rowInst parts g env) = true :=
      fun env henv => hall _ (hmem env henv)
    have hb : b = 1 := by
      have h1 := hcond 1 (by decide)
      cases hok : colorsOk (rowInst parts g 1)
      · simp [rowCond, threeColoring, feasibility, hok] at h1
      · simp [rowCond, threeColoring, feasibility, hok] at h1
        omega
    subst hb
    refine ⟨rfl, fun env henv => ?_⟩
    have h := hcond env henv
    by_cases h0 : env = 0
    · subst h0
      cases hok : colorsOk (rowInst parts g 0) <;>
        simp [rowCond, threeColoring, feasibility, hok] at h ⊢
    · cases hok : colorsOk (rowInst parts g env) <;>
        simp [rowCond, threeColoring, feasibility, hok, h0] at h ⊢
  · rintro ⟨rfl, hiff⟩
    refine ⟨⟨_, hmem 1 (by decide), rfl⟩, ?_⟩
    intro r hr
    obtain ⟨env, henv, rfl⟩ := List.mem_map.mp hr
    have henv' : env < 8 := by simpa [gadgetEnvs] using henv
    rw [rowInstP_threeColoring]
    by_cases h0 : env = 0
    · subst h0
      have hok : colorsOk (rowInst parts g 0) = false := by
        cases h : colorsOk (rowInst parts g 0)
        · rfl
        · exact absurd ((hiff 0 (by decide)).mp h) (by decide)
      simp [rowCond, threeColoring, feasibility, hok]
    · have hok : colorsOk (rowInst parts g env) = true := (hiff env henv').mpr h0
      simp [rowCond, threeColoring, feasibility, hok, h0]

/-- What "the row is 3-colorable" means: a choice of colors for all
    vertices of the universe that respects the pins of the row and gives
    adjacent vertices different colors. -/
theorem colorsOk_rowInst_iff (parts : List Nat) {g : List Edge}
    (hg : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges) (env : Nat) :
    colorsOk (rowInst parts g env) = true ↔
      ∃ f, SpecExt g (rowPins parts env) (threeColoring.attach parts).1.vertices [] f := by
  have hloop : ∀ a : Vertex, a ∉ adjTo g a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h <;> exact edges_ne (hg _ h) rfl
  exact colorable_iff_spec g _ (rowPins parts env) hloop (vertices_nodup _)

end Atlas.Meaning
