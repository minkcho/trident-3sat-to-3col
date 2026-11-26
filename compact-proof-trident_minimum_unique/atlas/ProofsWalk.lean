import atlas.ProofsPrune
import atlas.ProofsLib
/-!
  The walk theorems. `searchAux` is the pruned depth-first search over the
  free orbit switches.

  * `walkGraph` names the leaf graph of a branch (bit i of the mask decides
    orbit i, edges accumulated the way the walk accumulates them).
  * `searchAux_complete`: with a kill-sound pruning hypothesis, every mask
    whose leaf graph passes `checkGadget` is reported, for every mask (high
    bits are ignored by `walkGraph` exactly as the walk ignores them).
  * `threeColoring_kill` discharges the pruning hypothesis for 3-coloring
    from `colorsOk_antitone` and a `commonK` failure lemma, giving
    `searchSlice_exhaustive_threeColoring`: an empty found list means that
    no branch of the slice carries a valid gadget.
-/

namespace Atlas

open List

/-- The leaf graph of the branch selected by `mask`, accumulated the way
    the walk accumulates it (chosen orbits prepended onto `acc`). -/
def walkGraph (free : List (List Edge)) (mask : Nat) (acc : List Edge) :
    List Edge :=
  match free with
  | [] => acc
  | g :: rest =>
    if mask &&& 1 == 1 then walkGraph rest (mask >>> 1) (g ++ acc)
    else walkGraph rest (mask >>> 1) acc

theorem walkGraph_sublist :
    ∀ (free : List (List Edge)) (mask : Nat) (acc : List Edge),
      acc <+ walkGraph free mask acc := by
  intro free
  induction free with
  | nil => intro mask acc; exact List.Sublist.refl acc
  | cons g rest ih =>
    intro mask acc
    simp only [walkGraph]
    by_cases hb : mask &&& 1 == 1
    · rw [if_pos hb]
      exact (List.sublist_append_right g acc).trans (ih (mask >>> 1) (g ++ acc))
    · rw [if_neg hb]
      exact ih (mask >>> 1) acc

-- --------------------------------------------------- the walk, characterized

theorem searchAux_found_delta (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex)) :
    ∀ (free : List (List Edge)) (acc : List Edge) (stats : SliceStats),
      ∃ new, (searchAux P U anchors rows free acc stats).found
        = new ++ stats.found := by
  intro free
  induction free with
  | nil =>
    intro acc stats
    simp only [searchAux]
    cases checkGadget P U anchors rows acc with
    | some k => exact ⟨[(acc, k)], rfl⟩
    | none => exact ⟨[], rfl⟩
  | cons g rest ih =>
    intro acc stats
    simp only [searchAux]
    split
    · obtain ⟨n₁, h₁⟩ := ih (g ++ acc) stats
      obtain ⟨n₂, h₂⟩ := ih acc (searchAux P U anchors rows rest (g ++ acc) stats)
      exact ⟨n₂ ++ n₁, by rw [h₂, h₁, List.append_assoc]⟩
    · obtain ⟨n₂, h₂⟩ := ih acc _
      exact ⟨n₂, h₂⟩

/-- Completeness: with a kill-sound pruning bound, every branch whose leaf
    graph passes the check is reported -- pruning loses nothing. -/
theorem searchAux_complete (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex))
    (hkill : ∀ e e', e <+ e' →
      (rows.all fun r =>
        !r.1 || P.viable { verts := U.vertices, edges := e, anchors := anchors, selected := r.2.1, forbidden := r.2.2 }) = false →
      checkGadget P U anchors rows e' = none) :
    ∀ (free : List (List Edge)) (acc : List Edge) (stats : SliceStats)
      (mask k : Nat),
      checkGadget P U anchors rows (walkGraph free mask acc) = some k →
      (walkGraph free mask acc, k)
        ∈ (searchAux P U anchors rows free acc stats).found := by
  intro free
  induction free with
  | nil =>
    intro acc stats mask k hchk
    simp only [walkGraph] at hchk ⊢
    simp only [searchAux, hchk]
    exact List.mem_cons_self ..
  | cons g rest ih =>
    intro acc stats mask k hchk
    simp only [walkGraph] at hchk ⊢
    by_cases hb : mask &&& 1 == 1
    · rw [if_pos hb] at hchk ⊢
      simp only [searchAux]
      split
      · -- alive: the include-branch recursion finds it; the exclude-branch
        -- call afterwards only prepends more finds
        have hin := ih (g ++ acc) stats (mask >>> 1) k hchk
        obtain ⟨new, hnew⟩ := searchAux_found_delta P U anchors rows rest acc
          (searchAux P U anchors rows rest (g ++ acc) stats)
        rw [hnew]
        exact List.mem_append_right _ hin
      · -- pruned: the kill hypothesis contradicts the passing leaf
        next halive =>
        exfalso
        have hall : (rows.all fun r =>
            !r.1 || P.viable { verts := U.vertices, edges := g ++ acc, anchors := anchors, selected := r.2.1, forbidden := r.2.2 }) = false := by
          rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr halive) with ⟨_, h⟩
          exact h
        have := hkill (g ++ acc) (walkGraph rest (mask >>> 1) (g ++ acc))
          (walkGraph_sublist rest (mask >>> 1) (g ++ acc)) hall
        rw [this] at hchk
        cases hchk
    · rw [if_neg hb] at hchk ⊢
      simp only [searchAux]
      split
      · exact ih acc _ (mask >>> 1) k hchk
      · exact ih acc _ (mask >>> 1) k hchk

-- ------------------------------------------- the 3-coloring kill discharge

/-- If some satisfiable row of the table already fails, `commonK` fails:
    the 3-coloring measure of that row is zero, which no budget passes both
    the target and the faithful column with. -/
theorem commonK_none_3col {α : Type} [BEq α]
    {rows : List (Bool × Instance α)} {inst : Instance α}
    (hmem : (true, inst) ∈ rows) (hbad : colorsOk inst = false) :
    commonK threeColoring rows = none := by
  unfold commonK
  cases hfs : rows.findSome? fun r =>
      if r.1 then threeColoring.measure r.2 else none with
  | none => rfl
  | some k =>
    have hpred : ¬(((match threeColoring.measure inst with
        | some a => (!true || a == k) && threeColoring.target true k a
        | none => false) && (threeColoring.exact inst k == true)) = true) := by
      simp only [threeColoring, feasibility, hbad]
      simp
    have hbind : ∀ f : Nat → Option Nat, (some k >>= f) = f k := fun _ => rfl
    rw [hbind]
    dsimp only
    split
    · next hc =>
      exact absurd (List.all_eq_true.mp hc (true, inst) hmem) hpred
    · rfl

/-- The kill hypothesis of `searchAux_complete`, discharged for 3-coloring:
    a satisfiable row dead on a partial graph stays dead on every
    completion (P2's antitonicity), and a dead satisfiable row fails the
    whole table. -/
theorem threeColoring_kill (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex)) :
    ∀ e e', e <+ e' →
      (rows.all fun r =>
        !r.1 || threeColoring.viable
          { verts := U.vertices, edges := e, anchors := anchors, selected := r.2.1, forbidden := r.2.2 }) = false →
      checkGadget threeColoring U anchors rows e' = none := by
  intro e e' hsub hall
  obtain ⟨r, hr, hbad⟩ := List.all_eq_false.mp hall
  have hsat : r.1 = true := by
    cases h : r.1
    · rw [h] at hbad
      simp at hbad
    · rfl
  have hviab : colorsOk { verts := U.vertices, edges := e, anchors := anchors, selected := r.2.1, forbidden := r.2.2 } = false := by
    rw [hsat] at hbad
    cases h : colorsOk { verts := U.vertices, edges := e, anchors := anchors, selected := r.2.1, forbidden := r.2.2 }
    · rfl
    · exfalso
      apply hbad
      show (!true || threeColoring.viable _) = true
      simp only [threeColoring, feasibility]
      rw [h]
      rfl
  have hviab' : colorsOk { verts := U.vertices, edges := e', anchors := anchors, selected := r.2.1, forbidden := r.2.2 } = false := by
    cases h : colorsOk { verts := U.vertices, edges := e', anchors := anchors, selected := r.2.1, forbidden := r.2.2 }
    · rfl
    · exfalso
      have := colorsOk_antitone (i := { verts := U.vertices, edges := e, anchors := anchors, selected := r.2.1, forbidden := r.2.2 })
        (i' := { verts := U.vertices, edges := e', anchors := anchors, selected := r.2.1, forbidden := r.2.2 })
        rfl rfl rfl rfl hsub h
      rw [this] at hviab
      cases hviab
  unfold checkGadget
  apply commonK_none_3col (inst := { verts := U.vertices, edges := e', anchors := anchors, selected := r.2.1, forbidden := r.2.2 })
  · refine List.mem_map.mpr ⟨r, hr, ?_⟩
    rw [← hsat]
  · exact hviab'

-- ------------------------------------------------ slice-level exhaustiveness

/-- The P3 headline for 3-coloring: if the slice reports nothing, then NO
    branch of the walk -- equivalently, no subset of the free orbit
    switches -- carries a valid gadget. The negative claims of the paper
    become "this theorem plus one run". -/
theorem searchSlice_exhaustive_threeColoring (parts : List Nat)
    (symmetry : Bool) (mask k : Nat)
    (h : (searchSlice threeColoring parts symmetry).2.found = []) :
    checkGadget threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry)
      (walkGraph
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2
        mask
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1) ≠ some k := by
  intro hchk
  have hmem := searchAux_complete threeColoring (threeColoring.attach parts).1
    (anchorsOf parts.length (threeColoring.attach parts).1)
    (gadgetRows threeColoring symmetry)
    (threeColoring_kill _ _ _)
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).2
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).1
    { total := 2 ^ ((threeColoring.attach parts).1.splitForced
        (threeColoring.attach parts).2 symmetry).2.length }
    mask k hchk
  have hfound : (searchSlice threeColoring parts symmetry).2.found
      = ((searchAux threeColoring (threeColoring.attach parts).1
          (anchorsOf parts.length (threeColoring.attach parts).1)
          (gadgetRows threeColoring symmetry)
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).2
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).1
          { total := 2 ^ ((threeColoring.attach parts).1.splitForced
              (threeColoring.attach parts).2 symmetry).2.length }).found).reverse := by
    rfl
  rw [h] at hfound
  have := List.mem_reverse.mpr hmem
  rw [← hfound] at this
  cases this

end Atlas
