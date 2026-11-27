import search.Proofs
import search.ProofsSym

/-!
  What the statements mean. `Statement.lean` speaks about engine functions:
  `compositions`, the universe built by `threeColoring.attach`, and the
  judge `gadgetK`. The theorems below say, in plain terms, what the list of
  compositions and the judge are, so that a reader can check the statements
  without reading the engine.

  1. `mem_compositions_iff`: `compositions k [1, 2, 3, 6]` lists exactly the
     non-decreasing lists over {1, 2, 3, 6} summing to k. Nothing is missing,
     so "for every composition in the list" means "for every orbit
     composition".
  2. `gadgetK_some_iff`: `gadgetK threeColoring parts g false = some b`
     holds exactly when b = 1 and, for each of the eight inputs, the row is
     3-colorable iff the input satisfies the clause (`env ≠ 0`).
     `colorsOk_rowInst_iff` says what "the row is 3-colorable" means: a
     choice of colors 0, 1, 2 for every vertex that respects the pins (the
     anchors T, F, B; the true literals T; the false literals F) and gives
     adjacent vertices different colors.

  That the engine's action is an action of S3 by automorphisms of every
  symmetric candidate is part of `CandidateGadget.lean`, which turns a
  candidate into a gadget of Definition 1.
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
