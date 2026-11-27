import atlas.CandidateGraph

/-!
  Validity of a gadget is the engine's verdict on its candidate.

  For an input `env < 8`, bit `i` of `env` says whether literal `i` is true
  (`envInput`). A proper 3-coloring of the gadget that extends this input
  (`Gadget.Extends`, Definition 1) is the same thing as a coloring of the
  candidate that respects the pins of the row `env` (`SpecExt`):
  `specExt_iff_extends`. Hence a valid gadget passes the engine's judge:
  `gadgetK_of_valid`.
-/

namespace Def1

open Atlas

variable {V : Type}

/-- The literal coloring that the engine's input `env` encodes. -/
def envInput (env : Nat) : Fin 3 → Bool := fun i => env >>> i.val &&& 1 == 1

/-- Check of the encoding: an input below 8 has a true literal exactly when
    it is not 0. -/
theorem envInput_some_true : ∀ env, env < 8 →
    ((∃ i : Fin 3, envInput env i = true) ↔ env ≠ 0) := by decide

namespace Gadget

variable (g : Gadget V) [Finite V]

/-- The pins of the row `env`: the anchors are pinned to T, F, B (0, 1, 2)
    and literal `i` to T or F according to the input. -/
theorem rowPins_mem {env : Nat} {w : Vertex} {c : Nat} :
    (w, c) ∈ rowPins g.parts env ↔
      (w = g.toVertex g.gT ∧ c = 0) ∨ (w = g.toVertex g.gF ∧ c = 1) ∨
      (w = g.toVertex g.gB ∧ c = 2) ∨
      ∃ i : Fin 3, w = g.toVertex (g.lit i) ∧ c = if envInput env i then 0 else 1 := by
  rw [rowPins_eq, parts_length, toVertex_gT, toVertex_gF, toVertex_gB]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro (((h | h | h) | ⟨v, hv, rfl, rfl⟩) | ⟨v, hv, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨i, hi, hbit, rfl⟩ := mem_selected.mp hv
      refine Or.inr (Or.inr (Or.inr ⟨⟨i, hi⟩, (g.toVertex_lit ⟨i, hi⟩).symm, ?_⟩))
      show 0 = if (env >>> i &&& 1 == 1) = true then 0 else 1
      rw [if_pos hbit]
    · obtain ⟨i, hi, hbit, rfl⟩ := mem_forbidden.mp hv
      refine Or.inr (Or.inr (Or.inr ⟨⟨i, hi⟩, (g.toVertex_lit ⟨i, hi⟩).symm, ?_⟩))
      show 1 = if (env >>> i &&& 1 == 1) = true then 0 else 1
      rw [hbit]
      rfl
  · rintro (h | h | h | ⟨i, rfl, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
    · rw [toVertex_lit]
      by_cases hb : envInput env i = true
      · exact Or.inl (Or.inr ⟨.lit i.val, mem_selected.mpr ⟨i.val, i.isLt, hb, rfl⟩,
          rfl, by rw [if_pos hb]⟩)
      · exact Or.inr ⟨.lit i.val,
          mem_forbidden.mpr ⟨i.val, i.isLt, (Bool.not_eq_true _).mp hb, rfl⟩,
          rfl, by rw [if_neg hb]⟩

theorem colorAt_rowPins {env : Nat} {w : Vertex} {c : Nat} :
    colorAt (rowPins g.parts env) w = some c ↔
      (w = g.toVertex g.gT ∧ c = 0) ∨ (w = g.toVertex g.gF ∧ c = 1) ∨
      (w = g.toVertex g.gB ∧ c = 2) ∨
      ∃ i : Fin 3, w = g.toVertex (g.lit i) ∧ c = if envInput env i then 0 else 1 :=
  ⟨fun h => g.rowPins_mem.mp (mem_of_colorAt_eq_some h),
   fun h => colorAt_eq_some_of_mem (rowPins_keys_nodup g.parts env) (g.rowPins_mem.mpr h)⟩

/-- A coloring that respects the pins takes the pinned value. -/
theorem pin_eq {env : Nat} {f : Vertex → Nat} {w : Vertex} {c : Nat}
    (hp : pinOk (rowPins g.parts env) w (f w))
    (hc : colorAt (rowPins g.parts env) w = some c) : f w = c := by
  unfold pinOk at hp
  rw [hc] at hp
  exact hp

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
        rw [g.pin_eq hp hc]
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
    · exact Fin.ext (g.pin_eq (hpin _ (g.toVertex_mem _))
        (g.colorAt_rowPins.mpr (Or.inl ⟨rfl, rfl⟩)))
    · exact Fin.ext (g.pin_eq (hpin _ (g.toVertex_mem _))
        (g.colorAt_rowPins.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · exact Fin.ext (g.pin_eq (hpin _ (g.toVertex_mem _))
        (g.colorAt_rowPins.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · intro i
      have h := g.pin_eq (hpin _ (g.toVertex_mem (g.lit i)))
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

/-- A valid gadget (Definition 1) passes the engine's eight-row judge
    (by Statement 7). -/
theorem gadgetK_of_valid (hv : g.Valid) :
    gadgetK threeColoring g.parts g.edgeList false = some 1 := by
  obtain ⟨hjudge, hrow⟩ := Statement.gadgetK_is_validity g.parts g.edgeList 1
  refine hjudge.mpr ⟨rfl, fun env henv => ?_⟩
  rw [hrow g.symCandidate.1 env, ← envInput_some_true env henv, ← hv (envInput env)]
  exact g.specExt_iff_extends env

end Gadget

end Def1
