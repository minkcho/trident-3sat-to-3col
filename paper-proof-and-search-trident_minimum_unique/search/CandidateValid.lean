import search.CandidateGraph
import search.Rows

/-!
  Validity of a gadget is the engine's verdict on its candidate.

  For an input `env < 8`, bit `i` of `env` says whether literal `i` is true
  (`envInput`). A proper 3-coloring of the gadget that extends this input
  (`Gadget.Extends`, Definition 1) is the same thing as a coloring of the
  candidate that respects the pins of the row `env` (`SpecExt`):
  `specExt_iff_extends`. Hence a gadget is valid exactly when its candidate
  passes the engine's judge: `valid_iff`.
-/

namespace Def1

open Atlas

variable {V : Type}

namespace Gadget

variable (g : Gadget V) [Finite V]

/-- The pins of the row `env`: the anchors are pinned to T, F, B (0, 1, 2)
    and literal `i` to T or F according to the input. -/
theorem rowPins_mem {env : Nat} {w : Vertex} {c : Nat} :
    (w, c) ∈ rowPins g.parts env ↔
      (w = g.toVertex g.gT ∧ c = 0) ∨ (w = g.toVertex g.gF ∧ c = 1) ∨
      (w = g.toVertex g.gB ∧ c = 2) ∨
      ∃ i : Fin 3, w = g.toVertex (g.lit i) ∧ c = if envInput env i then 0 else 1 := by
  rw [rowPins_mem_iff, g.toVertex_gT, g.toVertex_gF, g.toVertex_gB, g.parts_length]
  simp only [g.toVertex_lit]

theorem colorAt_rowPins {env : Nat} {w : Vertex} {c : Nat} :
    colorAt (rowPins g.parts env) w = some c ↔
      (w = g.toVertex g.gT ∧ c = 0) ∨ (w = g.toVertex g.gF ∧ c = 1) ∨
      (w = g.toVertex g.gB ∧ c = 2) ∨
      ∃ i : Fin 3, w = g.toVertex (g.lit i) ∧ c = if envInput env i then 0 else 1 :=
  ⟨fun h => g.rowPins_mem.mp (mem_of_colorAt_eq_some h),
   fun h => colorAt_eq_some_of_mem (rowPins_keys_nodup g.parts env) (g.rowPins_mem.mpr h)⟩

/-- Definition 1 and the engine agree on a row: a proper 3-coloring of the
    gadget extending the input `env` exists exactly when a coloring of the
    candidate respects the pins of the row and gives adjacent vertices
    different colors. -/
theorem specExt_iff_extends (env : Nat) :
    (∃ f, SpecExt g.edgeList (rowPins g.parts env) g.U.vertices [] f) ↔
      g.Extends (envInput env) := by
  constructor
  · rintro ⟨f, hpin, hconf⟩
    -- every color is 0, 1 or 2
    have hval : ∀ w ∈ g.U.vertices, f w < 3 := by
      intro w hw
      have hp := hpin w hw
      cases hc : colorAt (rowPins g.parts env) w with
      | none =>
        unfold pinOk at hp
        rw [hc] at hp
        exact hp
      | some cp =>
        rw [pinOk_eq hp hc]
        rcases g.colorAt_rowPins.mp hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨i, _, rfl⟩
        · omega
        · omega
        · omega
        · split <;> omega
    refine ⟨fun v => ⟨f (g.toVertex v), hval _ (g.toVertex_mem v)⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro u v huv heq
      have hne := hconf (g.toVertex u) (g.toVertex_mem u) (g.toVertex v)
        (g.toVertex_mem_adjTo huv)
      unfold combined at hne
      rw [if_pos (g.toVertex_mem v)] at hne
      exact hne (congrArg some (congrArg Fin.val heq).symm)
    · exact Fin.ext (pinOk_eq (hpin _ (g.toVertex_mem _))
        (g.colorAt_rowPins.mpr (Or.inl ⟨rfl, rfl⟩)))
    · exact Fin.ext (pinOk_eq (hpin _ (g.toVertex_mem _))
        (g.colorAt_rowPins.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · exact Fin.ext (pinOk_eq (hpin _ (g.toVertex_mem _))
        (g.colorAt_rowPins.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · intro i
      have h := pinOk_eq (hpin _ (g.toVertex_mem (g.lit i)))
        (g.colorAt_rowPins.mpr (Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl⟩))))
      apply Fin.ext
      show f (g.toVertex (g.lit i)) = (if envInput env i = true then (0 : Fin 3) else 1).val
      rw [h]
      split <;> rfl
  · rintro ⟨c, hproper, hT, hF, hB, hlit⟩
    classical
    let f : Vertex → Nat := fun w =>
      if h : ∃ v, g.toVertex v = w then (c (Classical.choose h)).val else 0
    have hf : ∀ v, f (g.toVertex v) = (c v).val := by
      intro v
      have h : ∃ v', g.toVertex v' = g.toVertex v := ⟨v, rfl⟩
      show (if h : ∃ v', g.toVertex v' = g.toVertex v then (c (Classical.choose h)).val
        else 0) = (c v).val
      rw [dif_pos h, g.toVertex_injective (Classical.choose_spec h)]
    have hflt : ∀ w, f w < 3 := by
      intro w
      show (if h : ∃ v, g.toVertex v = w then (c (Classical.choose h)).val else 0) < 3
      split
      · exact (c _).isLt
      · omega
    refine ⟨f, ?_, ?_⟩
    · intro w _
      unfold pinOk
      cases hc : colorAt (rowPins g.parts env) w with
      | none => exact hflt w
      | some cp =>
        show f w = cp
        rcases g.colorAt_rowPins.mp hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
        · rw [hf, hT]
          rfl
        · rw [hf, hF]
          rfl
        · rw [hf, hB]
          rfl
        · rw [hf, hlit]
          split <;> rfl
    · intro w _ w' hw'
      obtain ⟨u, v, huv, rfl, rfl⟩ := g.adjTo_edgeList hw'
      unfold combined
      rw [if_pos (g.toVertex_mem v), hf, hf]
      intro h
      exact hproper u v huv (Fin.ext (Option.some.inj h).symm)

/-- A gadget (Definition 1) is valid exactly when its candidate passes the
    engine's eight-row judge (by `gadgetK_is_validity`). Every input of
    Definition 1 is the input of a row (`exists_env`). -/
theorem valid_iff :
    g.Valid ↔ gadgetK threeColoring g.parts g.edgeList false = some 1 := by
  obtain ⟨hjudge, hrow⟩ := Statement.gadgetK_is_validity g.parts g.edgeList 1
  rw [hjudge]
  constructor
  · intro hv
    refine ⟨rfl, fun env henv => ?_⟩
    rw [hrow g.symCandidate.1 env, ← envInput_some_true env henv, ← hv (envInput env)]
    exact g.specExt_iff_extends env
  · rintro ⟨-, h⟩ α
    obtain ⟨env, henv, rfl⟩ := exists_env α
    have h1 := h env henv
    rw [hrow g.symCandidate.1 env] at h1
    exact (g.specExt_iff_extends env).symm.trans
      (h1.trans (envInput_some_true env henv).symm)

end Gadget

end Def1
