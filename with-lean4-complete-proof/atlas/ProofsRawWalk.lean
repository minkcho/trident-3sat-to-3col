import Mathlib.Data.Fin.Tuple.Sort
import atlas.ProofsWalkBridge
import atlas.ProofsSym
import atlas.ProofsCover
/-!
  P3-4: the canonical raw walk, proved.

  `searchRawAux` (now total: structural recursion on the remaining tagged
  switches) is the orderly raw walk: it decides the framework attachments
  of aux 0, then aux 1, ..., and keeps a branch only while the attachment
  profiles are non-decreasing (`--no-symmetry` without `--no-canonical`).
  This file proves it sound (`searchRawAux_sound`), accounts for every
  branch (`searchRawAux_accounting`, prescribed bits discounted), and
  complete on sorted paths (`searchRawAux_complete`, under the same
  kill-sound pruning hypothesis as P3, discharged by `threeColoring_kill`).

  The canonical claim -- "at least one representative of every relabeling
  class survives" -- becomes a theorem in two steps: relabeling the
  in-gadget auxiliary vertices is invisible to the 3-coloring verifier
  (`gadgetK_relabel_3col`, through P4's `colorable_rename`), and a
  relabeling that sorts the profiles exists (`exists_sorting_perm`, from
  mathlib's `Tuple.sort`); the walk over the ordered switches then visits
  the sorted representative, because a vertex's profile is final once its
  group has been walked (`rawProfile_after_group`). Headlines:
  `searchSliceRaw_complete_threeColoring` -- every valid gadget of a raw
  slice is reported up to relabeling of the auxiliary vertices, with the
  same budget (the "30 finds / 4,740 finds" lists of the raw k = 4, 5 sweeps
  are complete up to relabeling) -- and `searchSliceRaw_exhaustive_threeColoring`
  (an empty canonical run rejects every graph of the slice). Scope: the raw
  slices of singleton auxiliary parts (`List.replicate own 1`), unsharded.
  Axioms: the standard three.
-/

namespace Atlas

open List

/-- The leaf graph of the raw branch selected by `mask` over the tagged
    switches (bit i decides switch i; chosen edges are consed onto `acc`,
    the way the walk accumulates them). -/
def walkRawGraph (remaining : List (Edge × Option Nat)) (mask : Nat)
    (acc : List Edge) : List Edge :=
  match remaining with
  | [] => acc
  | (e, _) :: rest =>
    if mask &&& 1 == 1 then walkRawGraph rest (mask >>> 1) (e :: acc)
    else walkRawGraph rest (mask >>> 1) acc

/-- Whether the sorted-profile checks along the branch of `mask` all
    pass: at a marker `some i` the profiles of aux i-1 and aux i, read
    off the edges chosen so far, are non-decreasing. -/
def SortedPath (fw : List Vertex) : List (Edge × Option Nat) → Nat → List Edge → Prop
  | [], _, _ => True
  | (e, mark) :: rest, mask, acc =>
    let acc' := if mask &&& 1 == 1 then e :: acc else acc
    (match mark with
      | some i => i == 0 ||
          rawProfile fw acc' (.aux (i - 1) 0) ≤ rawProfile fw acc' (.aux i 0)
      | none => true) = true ∧ SortedPath fw rest (mask >>> 1) acc'

-- ------------------------------------------------ the walk, characterized

/-- The found list only grows along the walk. -/
theorem searchRawAux_found_mono (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex))
    (fw : List Vertex) :
    ∀ (remaining : List (Edge × Option Nat)) (prescribe : List Bool)
      (acc : List Edge) (stats : SliceStats),
      stats.found <+ (searchRawAux P U anchors rows fw remaining prescribe acc stats).found := by
  intro remaining
  induction remaining with
  | nil =>
    intro prescribe acc stats
    simp only [searchRawAux]
    cases checkGadget P U anchors rows acc with
    | some k => exact List.sublist_cons_self _ _
    | none => exact List.Sublist.refl _
  | cons em rest ih =>
    intro prescribe acc stats
    obtain ⟨e, mark⟩ := em
    cases mark with
    | none =>
      cases prescribe with
      | cons b ps =>
        cases b <;> simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> exact ih ps _ stats
      | nil =>
        simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · exact (ih [] (e :: acc) stats).trans (ih [] acc _)
        · exact ih [] acc { stats with pruned := stats.pruned + 2 ^ (rest.length - Nat.min [].length rest.length) }
    | some i =>
      cases prescribe with
      | cons b ps =>
        cases b <;> simp only [searchRawAux, Bool.false_eq_true, ↓reduceIte] <;> split
        · exact List.Sublist.refl _
        · exact ih ps _ stats
        · exact List.Sublist.refl _
        · exact ih ps _ stats
      | nil =>
        simp only [searchRawAux]
        split
        · -- the exclude branch is pruned: the record keeps the include branch's finds
          split
          · split
            · exact List.Sublist.refl _
            · exact ih [] (e :: acc) stats
          · exact List.Sublist.refl _
        · split
          · split
            · exact ih [] acc { stats with pruned := stats.pruned + 2 ^ (rest.length - Nat.min [].length rest.length) }
            · exact (ih [] (e :: acc) stats).trans (ih [] acc _)
          · exact ih [] acc { stats with pruned := stats.pruned + 2 ^ (rest.length - Nat.min [].length rest.length) }

/-- Soundness: everything the raw walk reports passes the gadget check. -/
theorem searchRawAux_sound (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex))
    (fw : List Vertex) :
    ∀ (remaining : List (Edge × Option Nat)) (prescribe : List Bool)
      (acc : List Edge) (stats : SliceStats) (gk : List Edge × Nat),
      gk ∈ (searchRawAux P U anchors rows fw remaining prescribe acc stats).found →
      gk ∈ stats.found ∨ checkGadget P U anchors rows gk.1 = some gk.2 := by
  intro remaining
  induction remaining with
  | nil =>
    intro prescribe acc stats gk hmem
    simp only [searchRawAux] at hmem
    cases hchk : checkGadget P U anchors rows acc with
    | some k =>
      rw [hchk] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact Or.inr hchk
      · exact Or.inl hmem'
    | none =>
      rw [hchk] at hmem
      exact Or.inl hmem
  | cons em rest ih =>
    intro prescribe acc stats gk hmem
    obtain ⟨e, mark⟩ := em
    have comp : ∀ (acc₁ acc₂ : List Edge) (st : SliceStats),
        gk ∈ (searchRawAux P U anchors rows fw rest [] acc₂
          (searchRawAux P U anchors rows fw rest [] acc₁ st)).found →
        gk ∈ st.found ∨ checkGadget P U anchors rows gk.1 = some gk.2 := by
      intro acc₁ acc₂ st h
      rcases ih [] acc₂ _ gk h with h' | h'
      · exact ih [] acc₁ st gk h'
      · exact Or.inr h'
    have hrec : ∀ (acc' : List Edge) (st : SliceStats),
        gk ∈ (searchRawAux P U anchors rows fw rest [] acc' st).found →
        gk ∈ st.found ∨ checkGadget P U anchors rows gk.1 = some gk.2 :=
      fun acc' st h => ih [] acc' st gk h
    cases mark with
    | none =>
      cases prescribe with
      | cons b ps =>
        cases b <;> simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem <;> exact ih ps _ stats gk hmem
      | nil =>
        simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmem
        split at hmem
        · exact comp _ _ _ hmem
        · exact hrec acc { stats with pruned := stats.pruned + 2 ^ (rest.length - Nat.min [].length rest.length) } hmem
    | some i =>
      cases prescribe with
      | cons b ps =>
        cases b <;> simp only [searchRawAux, Bool.false_eq_true, ↓reduceIte] at hmem <;> split at hmem
        · exact Or.inl hmem
        · exact ih ps _ stats gk hmem
        · exact Or.inl hmem
        · exact ih ps _ stats gk hmem
      | nil =>
        simp only [searchRawAux] at hmem
        split at hmem
        · split at hmem
          · split at hmem
            · exact Or.inl hmem
            · exact hrec (e :: acc) stats hmem
          · exact Or.inl hmem
        · split at hmem
          · split at hmem
            · exact hrec acc { stats with pruned := stats.pruned + 2 ^ (rest.length - Nat.min [].length rest.length) } hmem
            · exact comp _ _ _ hmem
          · exact hrec acc { stats with pruned := stats.pruned + 2 ^ (rest.length - Nat.min [].length rest.length) } hmem

/-- The raw walk never touches `total`. -/
theorem searchRawAux_total (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex))
    (fw : List Vertex) :
    ∀ (remaining : List (Edge × Option Nat)) (prescribe : List Bool)
      (acc : List Edge) (stats : SliceStats),
      (searchRawAux P U anchors rows fw remaining prescribe acc stats).total
        = stats.total := by
  intro remaining
  induction remaining with
  | nil =>
    intro prescribe acc stats
    simp only [searchRawAux]
    cases checkGadget P U anchors rows acc <;> rfl
  | cons em rest ih =>
    intro prescribe acc stats
    obtain ⟨e, mark⟩ := em
    cases mark with
    | none =>
      cases prescribe with
      | cons b ps =>
        cases b <;> simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> exact ih ps _ stats
      | nil =>
        simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · rw [ih, ih]
        · rw [ih]
    | some i =>
      cases prescribe with
      | cons b ps =>
        cases b <;> simp only [searchRawAux, Bool.false_eq_true, ↓reduceIte] <;> split
        · rfl
        · exact ih ps _ stats
        · rfl
        · exact ih ps _ stats
      | nil =>
        simp only [searchRawAux]
        split
        · split
          · split
            · rfl
            · exact ih [] (e :: acc) stats
          · rfl
        · split
          · split
            · rw [ih]
            · rw [ih, ih]
          · rw [ih]

/-- The runtime guard's identity for the raw walk: every branch is a
    visited leaf or accounted to a pruned subtree, with the prescribed
    bits discounted. -/
theorem searchRawAux_accounting (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex))
    (fw : List Vertex) :
    ∀ (remaining : List (Edge × Option Nat)) (prescribe : List Bool)
      (acc : List Edge) (stats : SliceStats),
      (searchRawAux P U anchors rows fw remaining prescribe acc stats).leaves
          + (searchRawAux P U anchors rows fw remaining prescribe acc stats).pruned
        = stats.leaves + stats.pruned
          + 2 ^ (remaining.length - Nat.min prescribe.length remaining.length) := by
  intro remaining
  induction remaining with
  | nil =>
    intro prescribe acc stats
    simp only [searchRawAux, List.length_nil]
    cases checkGadget P U anchors rows acc <;> simp <;> omega
  | cons em rest ih =>
    intro prescribe acc stats
    obtain ⟨e, mark⟩ := em
    cases mark with
    | none =>
      cases prescribe with
      | cons b ps =>
        have hexp : rest.length + 1 - Nat.min (ps.length + 1) (rest.length + 1)
            = rest.length - Nat.min ps.length rest.length := by
          unfold Nat.min
          simp only [Nat.min_def]
          split <;> split <;> omega
        cases b <;> simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons, hexp] <;> exact ih ps _ stats
      | nil =>
        simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons,
          List.length_nil, Nat.zero_min, Nat.sub_zero, Nat.pow_succ]
        split
        · have h1 := ih [] (e :: acc) stats
          have h2 := ih [] acc (searchRawAux P U anchors rows fw rest [] (e :: acc) stats)
          simp only [List.length_nil, Nat.zero_min, Nat.sub_zero] at h1 h2
          omega
        · have h2 := ih [] acc { stats with pruned := stats.pruned + 2 ^ rest.length }
          simp only [List.length_nil, Nat.zero_min, Nat.sub_zero] at h2
          omega
    | some i =>
      cases prescribe with
      | cons b ps =>
        have hexp : rest.length + 1 - Nat.min (ps.length + 1) (rest.length + 1)
            = rest.length - Nat.min ps.length rest.length := by
          unfold Nat.min
          simp only [Nat.min_def]
          split <;> split <;> omega
        cases b <;> simp only [searchRawAux, Bool.false_eq_true, ↓reduceIte, List.length_cons, hexp] <;> split
        · simp only []; omega
        · exact ih ps _ stats
        · simp only []; omega
        · exact ih ps _ stats
      | nil =>
        simp only [searchRawAux, List.length_cons, List.length_nil, Nat.zero_min, Nat.sub_zero,
          Nat.pow_succ]
        split
        · split
          · split
            · simp only []; omega
            · have h1 := ih [] (e :: acc) stats
              simp only [List.length_nil, Nat.zero_min, Nat.sub_zero] at h1
              simp only []; omega
          · simp only []; omega
        · split
          · split
            · have h2 := ih [] acc { stats with pruned := stats.pruned + 2 ^ rest.length }
              simp only [List.length_nil, Nat.zero_min, Nat.sub_zero] at h2
              omega
            · have h1 := ih [] (e :: acc) stats
              have h2 := ih [] acc (searchRawAux P U anchors rows fw rest [] (e :: acc) stats)
              simp only [List.length_nil, Nat.zero_min, Nat.sub_zero] at h1 h2
              omega
          · have h2 := ih [] acc { stats with pruned := stats.pruned + 2 ^ rest.length }
            simp only [List.length_nil, Nat.zero_min, Nat.sub_zero] at h2
            omega

-- ------------------------------------------------ completeness on sorted paths

theorem walkRawGraph_sublist :
    ∀ (remaining : List (Edge × Option Nat)) (mask : Nat) (acc : List Edge),
      acc <+ walkRawGraph remaining mask acc := by
  intro remaining
  induction remaining with
  | nil => intro mask acc; exact List.Sublist.refl acc
  | cons em rest ih =>
    intro mask acc
    obtain ⟨e, mark⟩ := em
    simp only [walkRawGraph]
    by_cases hb : mask &&& 1 == 1
    · rw [if_pos hb]
      exact (List.sublist_cons_self e acc).trans (ih (mask >>> 1) (e :: acc))
    · rw [if_neg hb]
      exact ih (mask >>> 1) acc

/-- Completeness of the unsharded raw walk on sorted paths: with a
    kill-sound pruning bound, every branch whose sorted checks all pass and
    whose leaf graph passes the gadget check is reported. -/
theorem searchRawAux_complete (P : Problem) (U : Universe)
    (anchors : List Vertex) (rows : List (Bool × List Vertex × List Vertex))
    (fw : List Vertex)
    (hkill : ∀ e e', e <+ e' →
      (rows.all fun r =>
        !r.1 || P.viable { verts := U.vertices, edges := e, anchors := anchors, selected := r.2.1, forbidden := r.2.2 }) = false →
      checkGadget P U anchors rows e' = none) :
    ∀ (remaining : List (Edge × Option Nat)) (acc : List Edge) (stats : SliceStats)
      (mask k : Nat),
      SortedPath fw remaining mask acc →
      checkGadget P U anchors rows (walkRawGraph remaining mask acc) = some k →
      (walkRawGraph remaining mask acc, k)
        ∈ (searchRawAux P U anchors rows fw remaining [] acc stats).found := by
  intro remaining
  induction remaining with
  | nil =>
    intro acc stats mask k _ hchk
    simp only [walkRawGraph] at hchk ⊢
    simp only [searchRawAux, hchk]
    exact List.mem_cons_self ..
  | cons em rest ih =>
    intro acc stats mask k hsp hchk
    obtain ⟨e, mark⟩ := em
    obtain ⟨hsorted, hsp'⟩ := hsp
    simp only [walkRawGraph] at hchk ⊢
    -- membership survives the exclude branch's own bookkeeping
    have hmono := searchRawAux_found_mono P U anchors rows fw rest
    by_cases hb : mask &&& 1 == 1
    · -- the chosen edge is taken: the include branch finds the leaf
      rw [if_pos hb] at hchk hsp' hsorted ⊢
      have hin : (walkRawGraph rest (mask >>> 1) (e :: acc), k)
          ∈ (searchRawAux P U anchors rows fw rest [] (e :: acc) stats).found :=
        ih (e :: acc) stats (mask >>> 1) k hsp' hchk
      have halive : (decide (rest.length < pruneDepth) ||
          rows.all fun r => !r.1 || P.viable
            { verts := U.vertices, edges := e :: acc, anchors := anchors,
              selected := r.2.1, forbidden := r.2.2 }) = true := by
        cases h : (decide (rest.length < pruneDepth) ||
            rows.all fun r => !r.1 || P.viable
              { verts := U.vertices, edges := e :: acc, anchors := anchors,
                selected := r.2.1, forbidden := r.2.2 })
        · exfalso
          rcases Bool.or_eq_false_iff.mp h with ⟨_, hall⟩
          have := hkill (e :: acc) _ (walkRawGraph_sublist rest (mask >>> 1) (e :: acc)) hall
          rw [this] at hchk
          cases hchk
        · rfl
      cases mark with
      | none =>
        simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte, halive]
        exact (hmono [] acc _).subset hin
      | some i =>
        simp only [searchRawAux, halive, ↓reduceIte, hsorted, Bool.not_true, Bool.false_eq_true]
        split
        · exact hin
        · exact (hmono [] acc _).subset hin
    · rw [if_neg hb] at hchk hsp' hsorted ⊢
      have hin : ∀ st, (walkRawGraph rest (mask >>> 1) acc, k)
          ∈ (searchRawAux P U anchors rows fw rest [] acc st).found :=
        fun st => ih acc st (mask >>> 1) k hsp' hchk
      cases mark with
      | none =>
        simp only [searchRawAux, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hin _
      | some i =>
        simp only [searchRawAux, hsorted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact hin _

-- ------------------------------------------- relabeling the auxiliary vertices

/-- The raw universe of `own` singleton auxiliary parts, palette appended.
    ([opus5.5 review] was "`k`".) -/
abbrev rawU (own : Nat) : Universe := (threeColoring.attach (List.replicate own 1)).1

theorem rawU_parts (own : Nat) : (rawU own).parts = List.replicate own 1 ++ [1, 1, 1] :=
  attach_parts _

theorem getD_of_all_eq {a d : Nat} : ∀ (l : List Nat) (i : Nat), (∀ x ∈ l, x = a) →
    i < l.length → l.getD i d = a := by
  intro l
  induction l with
  | nil => intro i _ hi; cases hi
  | cons x l ih =>
    intro i hall hi
    cases i with
    | zero => exact hall x (List.mem_cons_self ..)
    | succ i =>
      exact ih i (fun y hy => hall y (List.mem_cons_of_mem _ hy)) (Nat.lt_of_succ_lt_succ hi)

theorem rawU_size {own p : Nat} (hp : p < own + 3) : (rawU own).size p = 1 := by
  unfold Universe.size
  rw [rawU_parts]
  apply getD_of_all_eq
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.eq_of_mem_replicate h
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with h | h | h <;> exact h
  · simp; omega

/-- The vertices of the raw universe: the three literals and `aux p 0` for
    `p < own + 3` (the last three are the palette anchors). -/
theorem mem_rawU {own : Nat} {v : Vertex} :
    v ∈ (rawU own).vertices ↔
      (∃ i, i < 3 ∧ v = .lit i) ∨ ∃ p, p < own + 3 ∧ v = .aux p 0 := by
  rw [mem_vertices]
  have hlen : (rawU own).parts.length = own + 3 := by rw [rawU_parts]; simp
  constructor
  · rintro (h | ⟨p, j, hp, hj, rfl⟩)
    · exact Or.inl h
    · rw [hlen] at hp
      rw [rawU_size hp] at hj
      have : j = 0 := by omega
      subst this
      exact Or.inr ⟨p, hp, rfl⟩
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, 0, by rw [hlen]; exact hp, by rw [rawU_size hp]; exact Nat.zero_lt_one, rfl⟩

/-- The framework vertices: literals and anchors. -/
theorem mem_rawFramework {own : Nat} {v : Vertex} :
    v ∈ rawFramework own (rawU own) ↔
      (∃ i, i < 3 ∧ v = .lit i) ∨ ∃ p, own ≤ p ∧ p < own + 3 ∧ v = .aux p 0 := by
  unfold rawFramework anchorsOf
  have hlen : (rawU own).parts.length = own + 3 := by rw [rawU_parts]; simp
  rw [hlen, List.mem_append, List.mem_map, List.mem_map]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact Or.inl ⟨i, List.mem_range.mp hi, rfl⟩
    · have := List.mem_range.mp hd
      exact Or.inr ⟨own + d, Nat.le_add_right _ _, by omega, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨p, hp1, hp2, rfl⟩)
    · exact Or.inl ⟨i, List.mem_range.mpr hi, rfl⟩
    · exact Or.inr ⟨p - own, List.mem_range.mpr (by omega), by
        rw [Nat.add_sub_cancel' hp1]⟩

theorem mem_rawFramework_vertices {own : Nat} {v : Vertex}
    (hv : v ∈ rawFramework own (rawU own)) : v ∈ (rawU own).vertices := by
  rcases mem_rawFramework.mp hv with ⟨i, hi, rfl⟩ | ⟨p, _, hp, rfl⟩
  · exact mem_rawU.mpr (Or.inl ⟨i, hi, rfl⟩)
  · exact mem_rawU.mpr (Or.inr ⟨p, hp, rfl⟩)

theorem rawU_legal (own : Nat) : (rawU own).legal := by
  apply attach_legal
  intro n hn
  exact Or.inl (List.eq_of_mem_replicate hn)

/-- A permutation of the auxiliary indices below `own`, with its inverse. -/
structure AuxPerm (own : Nat) where
  π : Nat → Nat
  π' : Nat → Nat
  lt : ∀ p, p < own → π p < own
  lt' : ∀ p, p < own → π' p < own
  left : ∀ p, p < own → π' (π p) = p
  right : ∀ p, p < own → π (π' p) = p

/-- Relabel the in-gadget auxiliary parts by `π` (identity elsewhere). -/
def relabelV (own : Nat) (π : Nat → Nat) : Vertex → Vertex
  | .aux p j => if p < own then .aux (π p) j else .aux p j
  | v => v

/-- The relabeled, renormalized edge list. -/
def relabelG (own : Nat) (π : Nat → Nat) (g : List Edge) : List Edge :=
  g.map fun e => normEdge (relabelV own π e.1, relabelV own π e.2)

theorem relabelV_aux_ge (own : Nat) (π : Nat → Nat) {p : Nat} (j : Nat) (hp : ¬p < own) :
    relabelV own π (.aux p j) = .aux p j := by
  simp [relabelV, hp]

theorem relabelV_aux_lt (own : Nat) (π : Nat → Nat) {p : Nat} (j : Nat) (hp : p < own) :
    relabelV own π (.aux p j) = .aux (π p) j := by
  simp [relabelV, hp]

/-- Framework vertices are fixed by every relabeling. -/
theorem relabelV_fw {own : Nat} (π : Nat → Nat) {v : Vertex}
    (hv : v ∈ rawFramework own (rawU own)) : relabelV own π v = v := by
  rcases mem_rawFramework.mp hv with ⟨i, _, rfl⟩ | ⟨p, hp, _, rfl⟩
  · rfl
  · exact relabelV_aux_ge own π 0 (Nat.not_lt.mpr hp)

/-- The inverse relabeling undoes the relabeling on every vertex. -/
theorem relabelV_inv (σ : AuxPerm own) (v : Vertex) :
    relabelV own σ.π' (relabelV own σ.π v) = v := by
  cases v with
  | lit i => rfl
  | aux p j =>
    by_cases hp : p < own
    · rw [relabelV_aux_lt own σ.π j hp, relabelV_aux_lt own σ.π' j (σ.lt p hp), σ.left p hp]
    · rw [relabelV_aux_ge own σ.π j hp, relabelV_aux_ge own σ.π' j hp]

theorem relabelV_inv' (σ : AuxPerm own) (v : Vertex) :
    relabelV own σ.π (relabelV own σ.π' v) = v := by
  cases v with
  | lit i => rfl
  | aux p j =>
    by_cases hp : p < own
    · rw [relabelV_aux_lt own σ.π' j hp, relabelV_aux_lt own σ.π j (σ.lt' p hp), σ.right p hp]
    · rw [relabelV_aux_ge own σ.π' j hp, relabelV_aux_ge own σ.π j hp]

theorem relabelV_inj (σ : AuxPerm own) {v w : Vertex}
    (h : relabelV own σ.π v = relabelV own σ.π w) : v = w := by
  have := congrArg (relabelV own σ.π') h
  rwa [relabelV_inv, relabelV_inv] at this

theorem relabelV_mem (σ : AuxPerm own) {v : Vertex} (hv : v ∈ (rawU own).vertices) :
    relabelV own σ.π v ∈ (rawU own).vertices := by
  rcases mem_rawU.mp hv with ⟨i, hi, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_rawU.mpr (Or.inl ⟨i, hi, rfl⟩)
  · by_cases hpo : p < own
    · rw [relabelV_aux_lt own σ.π 0 hpo]
      exact mem_rawU.mpr (Or.inr ⟨σ.π p, by have := σ.lt p hpo; omega, rfl⟩)
    · rw [relabelV_aux_ge own σ.π 0 hpo]
      exact mem_rawU.mpr (Or.inr ⟨p, hp, rfl⟩)

theorem relabelV_mem' (σ : AuxPerm own) {v : Vertex} (hv : v ∈ (rawU own).vertices) :
    relabelV own σ.π' v ∈ (rawU own).vertices := by
  rcases mem_rawU.mp hv with ⟨i, hi, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_rawU.mpr (Or.inl ⟨i, hi, rfl⟩)
  · by_cases hpo : p < own
    · rw [relabelV_aux_lt own σ.π' 0 hpo]
      exact mem_rawU.mpr (Or.inr ⟨σ.π' p, by have := σ.lt' p hpo; omega, rfl⟩)
    · rw [relabelV_aux_ge own σ.π' 0 hpo]
      exact mem_rawU.mpr (Or.inr ⟨p, hp, rfl⟩)

/-- Relabeling preserves the literal/auxiliary kind. -/
theorem relabelV_lit_iff (own : Nat) (π : Nat → Nat) (v : Vertex) :
    (∃ i, relabelV own π v = .lit i) ↔ ∃ i, v = .lit i := by
  cases v with
  | lit i => exact ⟨fun _ => ⟨i, rfl⟩, fun _ => ⟨i, rfl⟩⟩
  | aux p j =>
    constructor
    · rintro ⟨i, h⟩
      by_cases hp : p < own
      · rw [relabelV_aux_lt own π j hp] at h; cases h
      · rw [relabelV_aux_ge own π j hp] at h; cases h
    · rintro ⟨i, h⟩; cases h

theorem normEdge_cases (a b : Vertex) :
    normEdge (a, b) = (a, b) ∨ normEdge (a, b) = (b, a) := by
  unfold normEdge
  dsimp only
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Equal normal forms come from the same unordered pair ([opus5.5 review]
    was "iff": only this direction is stated). -/
theorem normEdge_pair_eq {a b c d : Vertex} (h : normEdge (a, b) = normEdge (c, d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold normEdge at h
  dsimp only at h
  split at h <;> split at h
  · exact Or.inl (Prod.mk.inj h)
  · exact Or.inr (Prod.mk.inj h)
  · exact Or.inr ⟨(Prod.mk.inj h).2, (Prod.mk.inj h).1⟩
  · exact Or.inl ⟨(Prod.mk.inj h).2, (Prod.mk.inj h).1⟩

/-- Membership in the relabeled list, spelled out. -/
theorem mem_relabelG {own : Nat} {π : Nat → Nat} {g : List Edge} {e : Edge} :
    e ∈ relabelG own π g ↔
      ∃ e' ∈ g, e = normEdge (relabelV own π e'.1, relabelV own π e'.2) := by
  unfold relabelG
  rw [List.mem_map]
  constructor
  · rintro ⟨e', he', rfl⟩; exact ⟨e', he', rfl⟩
  · rintro ⟨e', he', rfl⟩; exact ⟨e', he', rfl⟩

/-- Relabeling keeps the edges inside the universe's edge list. -/
theorem relabelG_sub_edges (σ : AuxPerm own) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (rawU own).edges) :
    ∀ e ∈ relabelG own σ.π g, e ∈ (rawU own).edges := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_relabelG.mp he
  have hU := rawU_legal own
  obtain ⟨h1, h2, _⟩ := mem_edges (hsub e' he')
  refine mem_edges_of_norm hU (relabelV_mem σ h1) (relabelV_mem σ h2)
    (fun h => edges_ne (hsub e' he') (relabelV_inj σ h)) ?_
  rintro i j ⟨hi, hj⟩
  obtain ⟨i', hi'⟩ := (relabelV_lit_iff own σ.π e'.1).mp ⟨i, hi⟩
  obtain ⟨j', hj'⟩ := (relabelV_lit_iff own σ.π e'.2).mp ⟨j, hj⟩
  exact lit_pair_not_mem rfl (hsub e' he') hi' hj'

-- ------------------------------------------------ the profiles transport

/-- `rawProfile` reads the graph only through the attachment edges. -/
theorem rawProfile_congr (fw : List Vertex) {g g' : List Edge} {v v' : Vertex}
    (h : ∀ w ∈ fw, g.contains (normEdge (v, w)) = g'.contains (normEdge (v', w))) :
    rawProfile fw g v = rawProfile fw g' v' := by
  unfold rawProfile
  have key : ∀ (L : List (Nat × Vertex)) (init : Nat), (∀ p ∈ L, p.2 ∈ fw) →
      L.foldl (fun m (p : Nat × Vertex) =>
          if g.contains (normEdge (v, p.2)) then m + 2 ^ p.1 else m) init
        = L.foldl (fun m (p : Nat × Vertex) =>
          if g'.contains (normEdge (v', p.2)) then m + 2 ^ p.1 else m) init := by
    intro L
    induction L with
    | nil => intros; rfl
    | cons p L ih =>
      intro init hL
      simp only [List.foldl_cons]
      rw [h p.2 (hL p (List.mem_cons_self ..))]
      exact ih _ (fun q hq => hL q (List.mem_cons_of_mem _ hq))
  exact key _ 0 (fun p hp => (List.of_mem_zip hp).2)

/-- The relabeled graph's profile at the relabeled vertex is the original
    profile. -/
theorem rawProfile_relabel (σ : AuxPerm own) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (rawU own).edges) {p : Nat} (hp : p < own) :
    rawProfile (rawFramework own (rawU own)) (relabelG own σ.π g) (.aux (σ.π p) 0)
      = rawProfile (rawFramework own (rawU own)) g (.aux p 0) := by
  apply rawProfile_congr
  intro w hw
  have hU := rawU_legal own
  have hwv : w ∈ (rawU own).vertices := mem_rawFramework_vertices hw
  have hpv : Vertex.aux p 0 ∈ (rawU own).vertices := mem_rawU.mpr (Or.inr ⟨p, by omega, rfl⟩)
  have hfix := relabelV_fw σ.π hw
  have hσp : relabelV own σ.π (.aux p 0) = .aux (σ.π p) 0 := relabelV_aux_lt own σ.π 0 hp
  cases hc : g.contains (normEdge (Vertex.aux p 0, w))
  · apply Bool.eq_false_iff.mpr
    intro hc'
    obtain ⟨e', he', heq⟩ := mem_relabelG.mp (List.contains_iff_mem.mp hc')
    obtain ⟨_, _, hn⟩ := mem_edges (hsub e' he')
    rw [← hσp, ← hfix] at heq
    have hmem : normEdge (Vertex.aux p 0, w) ∈ g := by
      rcases normEdge_pair_eq heq.symm with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have e1 := relabelV_inj σ ha
        have e2 := relabelV_inj σ hb
        rw [show normEdge (Vertex.aux p 0, w) = e' by rw [← hn, ← e1, ← e2]]
        exact he'
      · have e1 := relabelV_inj σ ha
        have e2 := relabelV_inj σ hb
        rw [show normEdge (Vertex.aux p 0, w) = e' by
          rw [← hn, normEdge_comm hU hpv hwv, ← e1, ← e2]]
        exact he'
    have := List.contains_iff_mem.mpr hmem
    rw [hc] at this
    cases this
  · apply List.contains_iff_mem.mpr
    have hmem := List.contains_iff_mem.mp hc
    refine mem_relabelG.mpr ⟨normEdge (Vertex.aux p 0, w), hmem, ?_⟩
    rcases normEdge_cases (Vertex.aux p 0) w with h | h
    · rw [h]
      dsimp only
      rw [hσp, hfix]
    · rw [h]
      dsimp only
      rw [hσp, hfix]
      have hσv : Vertex.aux (σ.π p) 0 ∈ (rawU own).vertices := hσp ▸ relabelV_mem σ hpv
      exact normEdge_comm hU hσv hwv

-- ------------------------------------------- gadgetK is relabeling-invariant

/-- Adjacency is orientation-free: normalizing the edges changes nothing. -/
theorem adjTo_relabelG (σ : AuxPerm own) (g : List Edge) (v u : Vertex) :
    u ∈ adjTo (relabelG own σ.π g) v ↔
      u ∈ adjTo (g.map fun e => (relabelV own σ.π e.1, relabelV own σ.π e.2)) v := by
  unfold relabelG
  rw [show (g.map fun e => normEdge (relabelV own σ.π e.1, relabelV own σ.π e.2))
      = (g.map fun e => (relabelV own σ.π e.1, relabelV own σ.π e.2)).map normEdge by
        rw [List.map_map]; rfl]
  exact adjTo_map_normEdge _ v u

/-- `colorsOk` on a raw-slice row is invariant under relabeling the
    auxiliary vertices: the pins sit on literals and anchors, which the
    relabeling fixes. -/
theorem colorsOk_relabel (σ : AuxPerm own) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (rawU own).edges) (anchors sel forb : List Vertex)
    (hanc : ∀ a ∈ anchors, a ∈ rawFramework own (rawU own))
    (hsel : ∀ v ∈ sel, ∃ i, i < 3 ∧ v = Vertex.lit i)
    (hforb : ∀ v ∈ forb, ∃ i, i < 3 ∧ v = Vertex.lit i) :
    colorsOk { verts := (rawU own).vertices, edges := relabelG own σ.π g, anchors := anchors, selected := sel, forbidden := forb } = colorsOk { verts := (rawU own).vertices, edges := g, anchors := anchors, selected := sel, forbidden := forb } := by
  unfold colorsOk
  dsimp only
  have hU := rawU_legal own
  have hpinfix : ∀ q ∈ anchors.zip [0, 1, 2] ++ sel.map ((·, 0)) ++ forb.map ((·, 1)),
      relabelV own σ.π q.1 = q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact relabelV_fw σ.π (hanc _ (List.of_mem_zip hq).1)
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
        obtain ⟨i, _, rfl⟩ := hsel v hv
        rfl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, _, rfl⟩ := hforb v hv
      rfl
  have hpinv : ∀ q ∈ anchors.zip [0, 1, 2] ++ sel.map ((·, 0)) ++ forb.map ((·, 1)),
      q.1 ∈ (rawU own).vertices := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact mem_rawFramework_vertices (hanc _ (List.of_mem_zip hq).1)
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
        obtain ⟨i, hi, rfl⟩ := hsel v hv
        exact mem_rawU.mpr (Or.inl ⟨i, hi, rfl⟩)
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, hi, rfl⟩ := hforb v hv
      exact mem_rawU.mpr (Or.inl ⟨i, hi, rfl⟩)
  have hedges : ∀ e ∈ g, e.1 ∈ (rawU own).vertices ∧ e.2 ∈ (rawU own).vertices :=
    fun e he => ⟨(mem_edges (hsub e he)).1, (mem_edges (hsub e he)).2.1⟩
  have hne : ∀ e ∈ g, e.1 ≠ e.2 := fun e he => edges_ne (hsub e he)
  have hnd := vertices_nodup (rawU own)
  have hren := colorable_rename (σ := relabelV own σ.π) (σ' := relabelV own σ.π')
    (fun v _ => relabelV_inv σ v) g (rawU own).vertices
    (anchors.zip [0, 1, 2] ++ sel.map ((·, 0)) ++ forb.map ((·, 1)))
    hedges hne (fun v hv => hv) hpinv hnd
  have hpinmap : (anchors.zip [0, 1, 2] ++ sel.map ((·, 0)) ++ forb.map ((·, 1))).map
      (fun q : Vertex × Nat => (relabelV own σ.π q.1, q.2))
      = anchors.zip [0, 1, 2] ++ sel.map ((·, 0)) ++ forb.map ((·, 1)) := by
    rw [List.map_congr_left (fun q hq =>
      (by rw [hpinfix q hq]; rfl : (relabelV own σ.π q.1, q.2) = id q)), List.map_id]
  rw [hpinmap] at hren
  have hvmem : ∀ u, u ∈ (rawU own).vertices.map (relabelV own σ.π) ↔ u ∈ (rawU own).vertices := by
    intro u
    constructor
    · intro h
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      exact relabelV_mem σ hw
    · intro h
      exact List.mem_map.mpr ⟨relabelV own σ.π' u, relabelV_mem' σ h, relabelV_inv' σ u⟩
  have hnd' : ((rawU own).vertices.map (relabelV own σ.π)).Nodup :=
    hnd.map_on (fun x _ y _ h => relabelV_inj σ h)
  have hloop : ∀ a : Vertex,
      a ∉ adjTo (g.map fun e => (relabelV own σ.π e.1, relabelV own σ.π e.2)) a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h <;> obtain ⟨e, he, heq⟩ := List.mem_map.mp h <;>
      exact hne e he (relabelV_inj σ ((Prod.mk.inj heq).1.trans (Prod.mk.inj heq).2.symm))
  rw [colorable_congr_verts _ _ hloop hnd' hnd hvmem] at hren
  rw [← hren]
  refine colorable_congr_edges _ _ ?_ hnd (fun v u => adjTo_relabelG σ g v u)
  intro a ha
  rcases mem_adjTo.mp ha with h | h <;>
    exact edges_ne (relabelG_sub_edges σ hsub _ h) rfl

/-- `checkGadget` on the raw eight-row table is relabeling-invariant. -/
theorem checkGadget_relabel_3col (σ : AuxPerm own) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (rawU own).edges) (anchors : List Vertex)
    (hanc : ∀ a ∈ anchors, a ∈ rawFramework own (rawU own)) :
    checkGadget threeColoring (rawU own) anchors (gadgetRows threeColoring false)
        (relabelG own σ.π g)
      = checkGadget threeColoring (rawU own) anchors (gadgetRows threeColoring false) g := by
  unfold checkGadget
  apply commonK_ext
  refine forall₂_map_map ?_
  intro r hr
  obtain ⟨isSat, sel, forb⟩ := r
  dsimp only
  have hrow : ∃ env, sel = (envSidesGadget threeColoring env).1 ∧
      forb = (envSidesGadget threeColoring env).2 := by
    unfold gadgetRows at hr
    obtain ⟨env, _, heq⟩ := List.mem_map.mp hr
    rcases hE : envSidesGadget threeColoring env with ⟨s, f⟩
    rw [hE] at heq
    simp only at heq
    obtain ⟨_, h2⟩ := Prod.mk.inj heq
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    exact ⟨env, by rw [hE, ← h3], by rw [hE, ← h4]⟩
  obtain ⟨env, hsel', hforb'⟩ := hrow
  have hsel : ∀ v ∈ sel, ∃ i, i < 3 ∧ v = Vertex.lit i := by
    intro v hv
    rw [hsel'] at hv
    obtain ⟨i, hi, _, rfl⟩ := mem_selected.mp hv
    exact ⟨i, hi, rfl⟩
  have hforb : ∀ v ∈ forb, ∃ i, i < 3 ∧ v = Vertex.lit i := by
    intro v hv
    rw [hforb'] at hv
    obtain ⟨i, hi, _, rfl⟩ := mem_forbidden.mp hv
    exact ⟨i, hi, rfl⟩
  have hco := colorsOk_relabel σ hsub anchors sel forb hanc hsel hforb
  refine ⟨rfl, ?_, ?_⟩
  · simp only [threeColoring, feasibility, hco]
  · intro k
    simp only [threeColoring, feasibility, hco]

/-- `gadgetK` on the raw slice is invariant under relabeling the auxiliary
    vertices: they carry no pins, so the verifier cannot tell them apart. -/
theorem gadgetK_relabel_3col (σ : AuxPerm own) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (rawU own).edges) :
    gadgetK threeColoring (List.replicate own 1) (relabelG own σ.π g) false
      = gadgetK threeColoring (List.replicate own 1) g false := by
  rw [gadgetK_3col_eq, gadgetK_3col_eq, List.length_replicate]
  exact checkGadget_relabel_3col σ hsub _ (fun a ha => List.mem_append_right _ ha)

-- ------------------------------------------------- a sorting relabeling

/-- A relabeling that sorts the profiles: read through `σ.π'`, `prof` is
    non-decreasing along the new indices. -/
theorem exists_sorting_perm (own : Nat) (prof : Nat → Nat) :
    ∃ σ : AuxPerm own, ∀ i, 0 < i → i < own → prof (σ.π' (i - 1)) ≤ prof (σ.π' i) := by
  let f : Fin own → Nat := fun i => prof i.val
  let τ := Tuple.sort f
  refine ⟨{ π := fun p => if h : p < own then (τ.symm ⟨p, h⟩).val else p,
            π' := fun p => if h : p < own then (τ ⟨p, h⟩).val else p,
            lt := fun p hp => by simp only [dif_pos hp]; exact (τ.symm ⟨p, hp⟩).isLt,
            lt' := fun p hp => by simp only [dif_pos hp]; exact (τ ⟨p, hp⟩).isLt,
            left := fun p hp => by
              simp only [dif_pos hp, dif_pos (τ.symm ⟨p, hp⟩).isLt, Fin.eta,
                Equiv.apply_symm_apply],
            right := fun p hp => by
              simp only [dif_pos hp, dif_pos (τ ⟨p, hp⟩).isLt, Fin.eta,
                Equiv.symm_apply_apply] }, ?_⟩
  intro i hi0 hi
  have hi1 : i - 1 < own := Nat.lt_of_le_of_lt (Nat.sub_le i 1) hi
  simp only [dif_pos hi, dif_pos hi1]
  exact Tuple.monotone_sort f (show (⟨i - 1, hi1⟩ : Fin own) ≤ ⟨i, hi⟩ from Nat.sub_le i 1)

-- ------------------------------------------- the walk over an append

theorem walkRawGraph_append :
    ∀ (l₁ l₂ : List (Edge × Option Nat)) (m : Nat) (acc : List Edge),
      walkRawGraph (l₁ ++ l₂) m acc
        = walkRawGraph l₂ (m >>> l₁.length) (walkRawGraph l₁ m acc) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ m acc; simp [walkRawGraph]
  | cons em rest ih =>
    intro l₂ m acc
    obtain ⟨e, mark⟩ := em
    simp only [List.cons_append, walkRawGraph, List.length_cons]
    rw [Nat.add_comm rest.length 1, Nat.shiftRight_add]
    split
    · exact ih l₂ (m >>> 1) (e :: acc)
    · exact ih l₂ (m >>> 1) acc

/-- The leaf's edges: the accumulator plus the chosen switches. -/
theorem mem_walkRawGraph_iff :
    ∀ (l : List (Edge × Option Nat)) (m : Nat) (acc : List Edge) (x : Edge),
      x ∈ walkRawGraph l m acc ↔
        x ∈ acc ∨ ∃ i, i < l.length ∧ (m >>> i &&& 1 == 1) = true ∧
          x = (l.getD i (default, none)).1 := by
  intro l
  induction l with
  | nil =>
    intro m acc x
    simp [walkRawGraph]
  | cons em rest ih =>
    intro m acc x
    obtain ⟨e, mark⟩ := em
    simp only [walkRawGraph]
    have hshift : ∀ i, (m >>> 1) >>> i = m >>> (i + 1) := by
      intro i; rw [Nat.add_comm i 1, Nat.shiftRight_add]
    constructor
    · intro hx
      split at hx
      · next hb =>
        rcases (ih (m >>> 1) (e :: acc) x).mp hx with hacc | ⟨i, hi, hbit, hxe⟩
        · rcases List.mem_cons.mp hacc with rfl | hacc'
          · exact Or.inr ⟨0, Nat.succ_pos _, by simpa using hb, rfl⟩
          · exact Or.inl hacc'
        · refine Or.inr ⟨i + 1, Nat.succ_lt_succ hi, ?_, hxe⟩
          rw [← hshift]; exact hbit
      · next hb =>
        rcases (ih (m >>> 1) acc x).mp hx with hacc | ⟨i, hi, hbit, hxe⟩
        · exact Or.inl hacc
        · refine Or.inr ⟨i + 1, Nat.succ_lt_succ hi, ?_, hxe⟩
          rw [← hshift]; exact hbit
    · rintro (hacc | ⟨i, hi, hbit, hxe⟩)
      · split
        · exact (ih _ _ x).mpr (Or.inl (List.mem_cons_of_mem _ hacc))
        · exact (ih _ _ x).mpr (Or.inl hacc)
      · cases i with
        | zero =>
          simp only [Nat.shiftRight_zero] at hbit
          rw [if_pos hbit]
          exact (ih _ _ x).mpr (Or.inl (by rw [hxe]; exact List.mem_cons_self ..))
        | succ i =>
          rw [← hshift] at hbit
          split
          · exact (ih _ _ x).mpr (Or.inr ⟨i, Nat.lt_of_succ_lt_succ hi, hbit, hxe⟩)
          · exact (ih _ _ x).mpr (Or.inr ⟨i, Nat.lt_of_succ_lt_succ hi, hbit, hxe⟩)

theorem mem_walkRawGraph_of {l : List (Edge × Option Nat)} {m : Nat} {acc : List Edge}
    {x : Edge} (hx : x ∈ walkRawGraph l m acc) : x ∈ acc ∨ x ∈ l.map (·.1) := by
  rcases (mem_walkRawGraph_iff l m acc x).mp hx with h | ⟨i, hi, _, rfl⟩
  · exact Or.inl h
  · right
    refine List.mem_map.mpr ⟨l.getD i (default, none), ?_, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi

-- --------------------------------------------- sorted paths, structurally

theorem walkRawGraph_cons (e : Edge) (mark : Option Nat) (rest : List (Edge × Option Nat))
    (m : Nat) (acc : List Edge) :
    walkRawGraph ((e, mark) :: rest) m acc
      = walkRawGraph rest (m >>> 1) (if m &&& 1 == 1 then e :: acc else acc) := by
  simp only [walkRawGraph]
  split <;> rfl

theorem SortedPath_append (fw : List Vertex) :
    ∀ (l₁ l₂ : List (Edge × Option Nat)) (m : Nat) (acc : List Edge),
      SortedPath fw (l₁ ++ l₂) m acc ↔
        SortedPath fw l₁ m acc ∧
          SortedPath fw l₂ (m >>> l₁.length) (walkRawGraph l₁ m acc) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ m acc; simp [SortedPath, walkRawGraph]
  | cons em rest ih =>
    intro l₂ m acc
    obtain ⟨e, mark⟩ := em
    simp only [List.cons_append, SortedPath, walkRawGraph_cons, List.length_cons]
    rw [Nat.add_comm rest.length 1, Nat.shiftRight_add, ih, and_assoc]

theorem SortedPath_of_noneMarks (fw : List Vertex) :
    ∀ (l : List (Edge × Option Nat)) (m : Nat) (acc : List Edge),
      (∀ x ∈ l, x.2 = none) → SortedPath fw l m acc := by
  intro l
  induction l with
  | nil => intros; trivial
  | cons em rest ih =>
    intro m acc hl
    obtain ⟨e, mark⟩ := em
    have hm : mark = none := hl (e, mark) (List.mem_cons_self ..)
    subst hm
    exact ⟨rfl, ih _ _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))⟩

/-- A path through a single marked switch: the check at the accumulated
    graph after it. -/
theorem SortedPath_single (fw : List Vertex) (e : Edge) (i m : Nat) (acc : List Edge) :
    SortedPath fw [(e, some i)] m acc ↔
      (i == 0 || rawProfile fw (walkRawGraph [(e, some i)] m acc) (.aux (i - 1) 0)
        ≤ rawProfile fw (walkRawGraph [(e, some i)] m acc) (.aux i 0)) = true := by
  simp only [SortedPath, walkRawGraph, and_true]
  split <;> rfl

-- ------------------------------------------ the ordered switches, named

/-- The index of an in-gadget auxiliary vertex (`none` on the framework). -/
def rawAuxIdx (own : Nat) : Vertex → Option Nat
  | .aux p _ => if p < own then some p else none
  | _ => none

/-- The attachments of auxiliary vertex `i` to the framework. -/
def rawExt (own : Nat) (U : Universe) (es : List Edge) (i : Nat) : List Edge :=
  es.filter fun e =>
    (rawAuxIdx own e.1 == some i && (rawFramework own U).contains e.2) ||
    (rawAuxIdx own e.2 == some i && (rawFramework own U).contains e.1)

/-- Group `i` of the orderly walk: its attachments, the last one marked. -/
def rawGroup (own : Nat) (U : Universe) (es : List Edge) (i : Nat) :
    List (Edge × Option Nat) :=
  match (rawExt own U es i).reverse with
  | [] => []
  | last :: front => front.reverse.map ((·, none)) ++ [(last, some i)]

def rawFwfw (own : Nat) (U : Universe) (es : List Edge) : List (Edge × Option Nat) :=
  (es.filter fun e => (rawFramework own U).contains e.1 && (rawFramework own U).contains e.2).map
    ((·, none))

def rawInternal (own : Nat) (es : List Edge) : List (Edge × Option Nat) :=
  (es.filter fun e => (rawAuxIdx own e.1).isSome && (rawAuxIdx own e.2).isSome).map ((·, none))

theorem rawOrderedSwitches_eq (own : Nat) (U : Universe) (free : List (List Edge)) :
    rawOrderedSwitches own U free
      = rawFwfw own U (free.flatMap id)
        ++ (List.range own).flatMap (rawGroup own U (free.flatMap id))
        ++ rawInternal own (free.flatMap id) := by
  unfold rawOrderedSwitches rawFwfw rawGroup rawExt rawInternal rawAuxIdx
  rfl

theorem rawAuxIdx_aux_lt (own : Nat) {p : Nat} (j : Nat) (hp : p < own) :
    rawAuxIdx own (.aux p j) = some p := by
  simp [rawAuxIdx, hp]

theorem rawAuxIdx_fw {own : Nat} {v : Vertex} (hv : v ∈ rawFramework own (rawU own)) :
    rawAuxIdx own v = none := by
  rcases mem_rawFramework.mp hv with ⟨i, _, rfl⟩ | ⟨p, hp, _, rfl⟩
  · rfl
  · simp [rawAuxIdx, Nat.not_lt.mpr hp]

/-- Every vertex of the raw universe is a framework vertex or an in-gadget
    auxiliary vertex. -/
theorem rawU_vertex_cases {own : Nat} {v : Vertex} (hv : v ∈ (rawU own).vertices) :
    v ∈ rawFramework own (rawU own) ∨ ∃ p, p < own ∧ v = .aux p 0 := by
  rcases mem_rawU.mp hv with ⟨i, hi, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl (mem_rawFramework.mpr (Or.inl ⟨i, hi, rfl⟩))
  · by_cases hpo : p < own
    · exact Or.inr ⟨p, hpo, rfl⟩
    · exact Or.inl (mem_rawFramework.mpr (Or.inr ⟨p, Nat.not_lt.mp hpo, hp, rfl⟩))

theorem mem_rawGroup_edge {own : Nat} {U : Universe} {es : List Edge} {i : Nat}
    {x : Edge × Option Nat} (hx : x ∈ rawGroup own U es i) :
    x.1 ∈ rawExt own U es i ∧ (x.2 = none ∨ x.2 = some i) := by
  unfold rawGroup at hx
  split at hx
  · cases hx
  · next last front hr =>
    have hext : rawExt own U es i = front.reverse ++ [last] := by
      rw [← List.reverse_reverse (rawExt own U es i), hr]
      simp
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact ⟨by rw [hext]; exact List.mem_append_left _ he, Or.inl rfl⟩
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨by rw [hext]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl), Or.inr rfl⟩

theorem mem_rawGroup_of_ext {own : Nat} {U : Universe} {es : List Edge} {i : Nat}
    {e : Edge} (he : e ∈ rawExt own U es i) :
    ∃ mk, (e, mk) ∈ rawGroup own U es i := by
  unfold rawGroup
  split
  · next hr =>
    rw [List.reverse_eq_nil_iff] at hr
    rw [hr] at he
    cases he
  · next last front hr =>
    have hext : rawExt own U es i = front.reverse ++ [last] := by
      rw [← List.reverse_reverse (rawExt own U es i), hr]
      simp
    rw [hext] at he
    rcases List.mem_append.mp he with he | he
    · exact ⟨none, List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)⟩
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨some i, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

/-- Every tagged switch carries a free edge (the converse is
    `mem_es_rawOrderedSwitches`; [opus5.5 review] was "exactly"). -/
theorem mem_rawOrderedSwitches_es {own : Nat} {free : List (List Edge)}
    {x : Edge × Option Nat} (hx : x ∈ rawOrderedSwitches own (rawU own) free) :
    x.1 ∈ free.flatMap id := by
  rw [rawOrderedSwitches_eq] at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact (List.mem_filter.mp he).1
    · obtain ⟨i, _, hxi⟩ := List.mem_flatMap.mp hx
      exact (List.mem_filter.mp (mem_rawGroup_edge hxi).1).1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact (List.mem_filter.mp he).1

theorem mem_es_rawOrderedSwitches {own : Nat} {free : List (List Edge)} {e : Edge}
    (hes : ∀ e ∈ free.flatMap id, e ∈ (rawU own).edges) (he : e ∈ free.flatMap id) :
    ∃ mk, (e, mk) ∈ rawOrderedSwitches own (rawU own) free := by
  rw [rawOrderedSwitches_eq]
  obtain ⟨h1, h2, _⟩ := mem_edges (hes e he)
  have hcont : ∀ v ∈ rawFramework own (rawU own), (rawFramework own (rawU own)).contains v = true :=
    fun v hv => List.contains_iff_mem.mpr hv
  rcases rawU_vertex_cases h1 with hf1 | ⟨p, hp, hv1⟩ <;>
    rcases rawU_vertex_cases h2 with hf2 | ⟨q, hq, hv2⟩
  · -- framework-framework
    refine ⟨none, List.mem_append_left _ (List.mem_append_left _ ?_)⟩
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by rw [hcont _ hf1, hcont _ hf2]; rfl⟩, rfl⟩
  · -- framework-aux q: group q
    obtain ⟨mk, hmk⟩ := mem_rawGroup_of_ext (own := own) (U := rawU own) (es := free.flatMap id)
      (i := q) (e := e) (List.mem_filter.mpr ⟨he, by
        rw [hv2, rawAuxIdx_aux_lt own 0 hq, hcont _ hf1]; simp⟩)
    exact ⟨mk, List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, hmk⟩))⟩
  · -- aux p-framework: group p
    obtain ⟨mk, hmk⟩ := mem_rawGroup_of_ext (own := own) (U := rawU own) (es := free.flatMap id)
      (i := p) (e := e) (List.mem_filter.mpr ⟨he, by
        rw [hv1, rawAuxIdx_aux_lt own 0 hp, hcont _ hf2]; simp⟩)
    exact ⟨mk, List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp, hmk⟩))⟩
  · -- aux-aux: internal
    refine ⟨none, List.mem_append_right _ ?_⟩
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by
      rw [hv1, hv2, rawAuxIdx_aux_lt own 0 hp, rawAuxIdx_aux_lt own 0 hq]; rfl⟩, rfl⟩

-- ------------------------------------------- the raw split of the edges

theorem mem_base_raw {U : Universe} {forced : List Edge} {e : Edge} :
    e ∈ (U.splitForced forced false).1 ↔
      e ∈ U.edges ∧ ((forced.map normEdge).any [e].contains) = true := by
  unfold Universe.splitForced
  simp only [Universe.switches, Bool.false_eq_true, ↓reduceIte]
  rw [List.mem_flatten]
  constructor
  · rintro ⟨o, ho, heo⟩
    obtain ⟨ho', hf⟩ := List.mem_filter.mp ho
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp ho'
    rw [List.mem_singleton] at heo
    subst heo
    exact ⟨he', hf⟩
  · rintro ⟨he, hf⟩
    exact ⟨[e], List.mem_filter.mpr ⟨List.mem_map.mpr ⟨e, he, rfl⟩, hf⟩, List.mem_singleton.mpr rfl⟩

theorem mem_es_raw {U : Universe} {forced : List Edge} {e : Edge} :
    e ∈ ((U.splitForced forced false).2).flatMap id ↔
      e ∈ U.edges ∧ ¬((forced.map normEdge).any [e].contains) = true := by
  unfold Universe.splitForced
  simp only [Universe.switches, Bool.false_eq_true, ↓reduceIte]
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨o, ho, heo⟩
    obtain ⟨ho', hf⟩ := List.mem_filter.mp ho
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp ho'
    simp only [id, List.mem_singleton] at heo
    subst heo
    exact ⟨he', by simpa using hf⟩
  · rintro ⟨he, hf⟩
    exact ⟨[e], List.mem_filter.mpr ⟨List.mem_map.mpr ⟨e, he, rfl⟩, by simpa using hf⟩,
      by simp⟩

theorem mem_free_raw {U : Universe} {forced : List Edge} {o : List Edge}
    (ho : o ∈ (U.splitForced forced false).2) : ∃ e ∈ U.edges, o = [e] := by
  unfold Universe.splitForced at ho
  simp only [Universe.switches, Bool.false_eq_true, ↓reduceIte] at ho
  obtain ⟨ho', _⟩ := List.mem_filter.mp ho
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho'
  exact ⟨e, he, rfl⟩

/-- The forced palette edges of the raw slice join framework vertices. -/
theorem forced_raw_fw {own : Nat} {f : Edge}
    (hf : f ∈ (threeColoring.attach (List.replicate own 1)).2) :
    f.1 ∈ rawFramework own (rawU own) ∧ f.2 ∈ rawFramework own (rawU own) := by
  simp only [threeColoring, feasibility, List.length_replicate, List.mem_cons,
    List.mem_nil_iff, or_false] at hf
  have anc : ∀ d, d < 3 → Vertex.aux (own + d) 0 ∈ rawFramework own (rawU own) :=
    fun d hd => mem_rawFramework.mpr (Or.inr ⟨own + d, Nat.le_add_right _ _, by omega, rfl⟩)
  have lit : ∀ i, i < 3 → Vertex.lit i ∈ rawFramework own (rawU own) :=
    fun i hi => mem_rawFramework.mpr (Or.inl ⟨i, hi, rfl⟩)
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simpa using anc 0 (by decide), anc 1 (by decide)⟩
  · exact ⟨anc 1 (by decide), anc 2 (by decide)⟩
  · exact ⟨anc 2 (by decide), by simpa using anc 0 (by decide)⟩
  · exact ⟨lit 0 (by decide), anc 2 (by decide)⟩
  · exact ⟨lit 1 (by decide), anc 2 (by decide)⟩
  · exact ⟨lit 2 (by decide), anc 2 (by decide)⟩

theorem base_raw_fw {own : Nat} {e : Edge}
    (he : e ∈ ((rawU own).splitForced (threeColoring.attach (List.replicate own 1)).2 false).1) :
    e.1 ∈ rawFramework own (rawU own) ∧ e.2 ∈ rawFramework own (rawU own) := by
  obtain ⟨_, hf⟩ := mem_base_raw.mp he
  obtain ⟨f', hf', hc⟩ := List.any_eq_true.mp hf
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
  have hef : e = normEdge f := by
    have := List.contains_iff_mem.mp hc
    rw [List.mem_singleton] at this
    exact this.symm
  obtain ⟨h1, h2⟩ := forced_raw_fw hf
  rcases normEdge_cases f.1 f.2 with h | h <;> rw [hef, h]
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

-- ------------------------------------------- sorted paths through the groups

/-- A group's path is sorted as soon as its marker check holds at the
    accumulated graph after the group. -/
theorem SortedPath_group_of (fw : List Vertex) (own : Nat) (U : Universe) (es : List Edge)
    (i m : Nat) (acc : List Edge)
    (hcond : (i == 0 ||
      rawProfile fw (walkRawGraph (rawGroup own U es i) m acc) (.aux (i - 1) 0)
        ≤ rawProfile fw (walkRawGraph (rawGroup own U es i) m acc) (.aux i 0)) = true) :
    SortedPath fw (rawGroup own U es i) m acc := by
  rcases hr : (rawExt own U es i).reverse with _ | ⟨last, front⟩
  · simp only [rawGroup, hr]
    trivial
  · simp only [rawGroup, hr] at hcond ⊢
    rw [SortedPath_append]
    refine ⟨SortedPath_of_noneMarks fw _ _ _ ?_, ?_⟩
    · intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      rfl
    · rw [SortedPath_single, ← walkRawGraph_append]
      exact hcond

/-- The groups' paths are sorted when every marker check holds at the
    graph accumulated through that group. -/
theorem SortedPath_groups (fw : List Vertex) (own : Nat) (U : Universe) (es : List Edge)
    (m : Nat) (acc : List Edge)
    (hcond : ∀ n, n < own → (n == 0 ||
      rawProfile fw (walkRawGraph ((List.range (n + 1)).flatMap (rawGroup own U es)) m acc)
          (.aux (n - 1) 0)
        ≤ rawProfile fw (walkRawGraph ((List.range (n + 1)).flatMap (rawGroup own U es)) m acc)
          (.aux n 0)) = true) :
    ∀ n, n ≤ own → SortedPath fw ((List.range n).flatMap (rawGroup own U es)) m acc := by
  intro n
  induction n with
  | zero => intro _; simp [SortedPath]
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      SortedPath_append]
    refine ⟨ih (Nat.le_of_succ_le hn), SortedPath_group_of fw own U es n _ _ ?_⟩
    rw [← walkRawGraph_append, ← List.append_nil (rawGroup own U es n),
      ← List.flatMap_nil (f := rawGroup own U es), ← List.flatMap_cons, ← List.flatMap_append,
      ← List.range_succ]
    exact hcond n hn

-- ------------------------------------ the profiles stabilize after a group

/-- The edges walked after group `n` never attach an auxiliary vertex
    `j ≤ n` to the framework. -/
theorem suffix_no_attach {own : Nat} {free : List (List Edge)} {n j : Nat} (hn : n < own)
    (hj : j ≤ n) {w : Vertex} (hw : w ∈ rawFramework own (rawU own)) {x : Edge × Option Nat}
    (hx : x ∈ (List.range' (n + 1) (own - (n + 1))).flatMap
        (rawGroup own (rawU own) (free.flatMap id)) ++ rawInternal own (free.flatMap id)) :
    x.1 ≠ normEdge (Vertex.aux j 0, w) := by
  intro heq
  have hjidx : rawAuxIdx own (Vertex.aux j 0) = some j := rawAuxIdx_aux_lt own 0 (by omega)
  have hwidx : rawAuxIdx own w = none := rawAuxIdx_fw hw
  have hwfw : (rawFramework own (rawU own)).contains w = true := List.contains_iff_mem.mpr hw
  -- the two orientations of the attachment edge
  have hends : (x.1.1 = Vertex.aux j 0 ∧ x.1.2 = w) ∨ (x.1.1 = w ∧ x.1.2 = Vertex.aux j 0) := by
    rcases normEdge_cases (Vertex.aux j 0) w with h | h <;> rw [h] at heq
    · exact Or.inl ⟨by rw [heq], by rw [heq]⟩
    · exact Or.inr ⟨by rw [heq], by rw [heq]⟩
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i', hi', hxi⟩ := List.mem_flatMap.mp hx
    have hi'n : n + 1 ≤ i' := by
      obtain ⟨d, _, rfl⟩ := List.mem_range'.mp hi'
      omega
    have hext := (List.mem_filter.mp (mem_rawGroup_edge hxi).1).2
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hext <;>
      simp [hjidx, hwidx] at hext <;> omega
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have hint := (List.mem_filter.mp he).2
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at h1 h2 <;> rw [h1, h2] at hint <;>
      simp [hjidx, hwidx] at hint

/-- `rawProfile` of `aux j 0` is already final after group `n ≥ j`. -/
theorem rawProfile_after_group {own : Nat} {free : List (List Edge)} (m : Nat)
    (base : List Edge) {n j : Nat} (hn : n < own) (hj : j ≤ n) :
    rawProfile (rawFramework own (rawU own))
        (walkRawGraph (rawFwfw own (rawU own) (free.flatMap id)
          ++ (List.range (n + 1)).flatMap (rawGroup own (rawU own) (free.flatMap id))) m base)
        (.aux j 0)
      = rawProfile (rawFramework own (rawU own))
        (walkRawGraph (rawOrderedSwitches own (rawU own) free) m base) (.aux j 0) := by
  have hsplit : rawOrderedSwitches own (rawU own) free
      = (rawFwfw own (rawU own) (free.flatMap id)
          ++ (List.range (n + 1)).flatMap (rawGroup own (rawU own) (free.flatMap id)))
        ++ ((List.range' (n + 1) (own - (n + 1))).flatMap (rawGroup own (rawU own) (free.flatMap id))
          ++ rawInternal own (free.flatMap id)) := by
    rw [rawOrderedSwitches_eq, List.range_eq_range',
      show List.range' 0 own = List.range' 0 (n + 1) ++ List.range' (n + 1) (own - (n + 1)) by
        have := @List.range'_append 0 (n + 1) (own - (n + 1)) 1
        rw [Nat.zero_add, Nat.one_mul, Nat.add_sub_cancel' hn] at this
        exact this.symm,
      List.flatMap_append, ← List.range_eq_range']
    simp only [List.append_assoc]
  apply rawProfile_congr
  intro w hw
  rw [hsplit]
  conv_rhs => rw [walkRawGraph_append]
  cases hc : (walkRawGraph (rawFwfw own (rawU own) (free.flatMap id)
      ++ (List.range (n + 1)).flatMap (rawGroup own (rawU own) (free.flatMap id))) m base).contains
      (normEdge (Vertex.aux j 0, w))
  · refine (Bool.eq_false_iff.mpr ?_).symm
    intro hc'
    rcases mem_walkRawGraph_of (List.contains_iff_mem.mp hc') with hin | hin
    · have := List.contains_iff_mem.mpr hin
      rw [hc] at this
      cases this
    · obtain ⟨x, hx, hx1⟩ := List.mem_map.mp hin
      exact suffix_no_attach hn hj hw hx hx1
  · exact (List.contains_iff_mem.mpr
      ((walkRawGraph_sublist _ _ _).subset (List.contains_iff_mem.mp hc))).symm

-- ---------------------------------------- the canonical run, unfolded

theorem searchSliceRaw_found_eq (own : Nat) :
    (searchSliceRaw threeColoring (List.replicate own 1)).2.found
      = ((searchRawAux threeColoring (rawU own) (anchorsOf own (rawU own))
          (gadgetRows threeColoring false) (rawFramework own (rawU own))
          (rawOrderedSwitches own (rawU own)
            ((rawU own).splitForced (threeColoring.attach (List.replicate own 1)).2 false).2)
          [] ((rawU own).splitForced (threeColoring.attach (List.replicate own 1)).2 false).1
          { total := 2 ^ (((rawU own).splitForced
              (threeColoring.attach (List.replicate own 1)).2 false).2.length - 0) }).found).reverse := by
  have hlog : Nat.log2 1 = 0 := by simpa using Nat.log2_two_pow (n := 0)
  have hneg : negLayerOk threeColoring (rawU own) = true := rfl
  unfold searchSliceRaw
  simp only [List.length_replicate, hlog, Nat.zero_min, Nat.lt_irrefl, decide_false,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.range_zero, List.map_nil, hneg,
    Bool.not_true]

/-- Membership in the enumerated candidates, in projection form (the
    split is not unfolded). -/
theorem mem_graphs_iff' {U : Universe} {sym : Bool} {forced : List Edge} {g : List Edge} :
    g ∈ U.graphs sym forced ↔
      ∃ mask, mask < 2 ^ (U.splitForced forced sym).2.length ∧
        g = graphAt (U.splitForced forced sym).1 (U.splitForced forced sym).2 mask := by
  unfold Universe.graphs
  rw [List.mem_map]
  constructor
  · rintro ⟨mask, hm, rfl⟩
    exact ⟨mask, List.mem_range.mp hm, rfl⟩
  · rintro ⟨mask, hm, rfl⟩
    exact ⟨mask, List.mem_range.mpr hm, rfl⟩

-- ------------------------------------------------- the canonical headline

set_option maxHeartbeats 1000000 in
/-- P3-4 headline, completeness up to relabeling: every valid gadget of the
    raw slice has a relabeling of its auxiliary vertices whose edge set the
    canonical run reports, with the same budget -- the orderly walk's
    pruning of unsorted branches loses nothing (`gadgetK_relabel_3col`
    makes the relabeling invisible to the verifier, and a sorted
    representative of every graph is walked). -/
theorem searchSliceRaw_complete_threeColoring (own : Nat) :
    ∀ g ∈ (rawU own).graphs (symmetry := false)
        (forced := (threeColoring.attach (List.replicate own 1)).2),
      ∀ k, gadgetK threeColoring (List.replicate own 1) g false = some k →
        ∃ σ : AuxPerm own, ∃ L, (L, k) ∈ (searchSliceRaw threeColoring (List.replicate own 1)).2.found ∧
          ∀ e, e ∈ L ↔ e ∈ relabelG own σ.π g := by
  intro g hg k hk
  rw [searchSliceRaw_found_eq]
  obtain ⟨mask, _, rfl⟩ := mem_graphs_iff'.mp hg
  set forced := (threeColoring.attach (List.replicate own 1)).2 with hforced
  set base := ((rawU own).splitForced forced false).1 with hbase
  set free := ((rawU own).splitForced forced false).2 with hfree
  set fw := rawFramework own (rawU own) with hfw
  set tagged := rawOrderedSwitches own (rawU own) free with htagged
  have hU := rawU_legal own
  -- the graph lives inside the edge list and contains the base
  have hes : ∀ e ∈ free.flatMap id, e ∈ (rawU own).edges := fun e he => (mem_es_raw.mp he).1
  have hsub : ∀ e ∈ graphAt base free mask, e ∈ (rawU own).edges := by
    intro e he
    rcases (mem_graphAt_iff base free mask e).mp he with hb | ⟨o, ho, heo⟩
    · exact (mem_base_raw.mp hb).1
    · obtain ⟨e', he', rfl⟩ := mem_free_raw ((bitSubset_sublist mask free).subset ho)
      rw [List.mem_singleton] at heo
      rw [heo]; exact he'
  have hbaseg : ∀ e ∈ base, e ∈ graphAt base free mask :=
    fun e he => (mem_graphAt_iff base free mask e).mpr (Or.inl he)
  -- the sorting relabeling
  obtain ⟨σ, hσ⟩ := exists_sorting_perm own (fun p => rawProfile fw (graphAt base free mask) (.aux p 0))
  set g' := relabelG own σ.π (graphAt base free mask) with hg'
  have hsub' : ∀ e ∈ g', e ∈ (rawU own).edges := relabelG_sub_edges σ hsub
  have hmono : ∀ i, 0 < i → i < own →
      rawProfile fw g' (.aux (i - 1) 0) ≤ rawProfile fw g' (.aux i 0) := by
    intro i hi0 hi
    have e1 : rawProfile fw g' (.aux (i - 1) 0)
        = rawProfile fw (graphAt base free mask) (.aux (σ.π' (i - 1)) 0) := by
      have := rawProfile_relabel σ hsub (σ.lt' _ (by omega : i - 1 < own))
      rw [σ.right _ (by omega)] at this
      exact this
    have e2 : rawProfile fw g' (.aux i 0)
        = rawProfile fw (graphAt base free mask) (.aux (σ.π' i) 0) := by
      have := rawProfile_relabel σ hsub (σ.lt' _ hi)
      rw [σ.right _ hi] at this
      exact this
    rw [e1, e2]
    exact hσ i hi0 hi
  have hbase' : ∀ e ∈ base, e ∈ g' := by
    intro e he
    obtain ⟨hf1, hf2⟩ := base_raw_fw he
    refine mem_relabelG.mpr ⟨e, hbaseg e he, ?_⟩
    rw [relabelV_fw σ.π hf1, relabelV_fw σ.π hf2]
    exact ((mem_edges (hsub e (hbaseg e he))).2.2).symm
  -- the mask whose leaf is g' as a set
  obtain ⟨m, _, hm⟩ := exists_env_of_bits
    (fun i => decide ((tagged.getD i (default, none)).1 ∈ g')) tagged.length
  set L := walkRawGraph tagged m base with hL
  have hLg : ∀ e, e ∈ L ↔ e ∈ g' := by
    intro e
    rw [hL, mem_walkRawGraph_iff]
    constructor
    · rintro (hb | ⟨i, hi, hbit, rfl⟩)
      · exact hbase' e hb
      · rw [bit_eq_testBit, hm i hi] at hbit
        exact of_decide_eq_true hbit
    · intro heg
      have heE := hsub' e heg
      by_cases hb : e ∈ base
      · exact Or.inl hb
      · have hes' : e ∈ free.flatMap id := by
          refine mem_es_raw.mpr ⟨heE, ?_⟩
          intro hf
          exact hb (mem_base_raw.mpr ⟨heE, hf⟩)
        obtain ⟨mk, hmk⟩ := mem_es_rawOrderedSwitches hes hes'
        obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp hmk
        refine Or.inr ⟨i, hi, ?_, ?_⟩
        · rw [bit_eq_testBit, hm i hi]
          apply decide_eq_true
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hti]
          exact heg
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hti]
  have hLsub : ∀ e ∈ L, e ∈ (rawU own).edges := fun e he => hsub' e ((hLg e).mp he)
  have hloopL : ∀ e ∈ L, e.1 ≠ e.2 := fun e he => edges_ne (hLsub e he)
  -- the leaf's profiles are g''s
  have hprofL : ∀ j, rawProfile fw L (.aux j 0) = rawProfile fw g' (.aux j 0) := by
    intro j
    apply rawProfile_congr
    intro w _
    cases hc : g'.contains (normEdge (Vertex.aux j 0, w))
    · refine Bool.eq_false_iff.mpr (fun hc' => ?_)
      have := List.contains_iff_mem.mpr ((hLg _).mp (List.contains_iff_mem.mp hc'))
      rw [hc] at this
      cases this
    · exact List.contains_iff_mem.mpr ((hLg _).mpr (List.contains_iff_mem.mp hc))
  -- the branch of the mask is sorted
  have hsorted : SortedPath fw tagged m base := by
    rw [htagged, rawOrderedSwitches_eq, SortedPath_append, SortedPath_append]
    refine ⟨⟨SortedPath_of_noneMarks _ _ _ _ ?_, ?_⟩, SortedPath_of_noneMarks _ _ _ _ ?_⟩
    · intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      rfl
    · refine SortedPath_groups fw own (rawU own) (free.flatMap id) _ _ ?_ own (Nat.le_refl _)
      intro n hn
      by_cases hn0 : n = 0
      · subst hn0
        rfl
      · rw [← walkRawGraph_append, rawProfile_after_group m base hn (Nat.sub_le n 1),
          rawProfile_after_group m base hn (Nat.le_refl n)]
        have hp1 := hprofL (n - 1)
        have hp2 := hprofL n
        rw [hL, htagged] at hp1 hp2
        rw [hp1, hp2, decide_eq_true (hmono n (Nat.pos_of_ne_zero hn0) hn), Bool.or_true]
    · intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      rfl
  -- the leaf passes exactly when g' does
  have hcheck : checkGadget threeColoring (rawU own) (anchorsOf own (rawU own))
        (gadgetRows threeColoring false) L
      = checkGadget threeColoring (rawU own) (anchorsOf own (rawU own))
        (gadgetRows threeColoring false) g' :=
    checkGadget_congr_3col _ _ _ hloopL hLg
  have hgk : gadgetK threeColoring (List.replicate own 1) (graphAt base free mask) false
      = checkGadget threeColoring (rawU own) (anchorsOf own (rawU own))
          (gadgetRows threeColoring false) g' := by
    rw [← gadgetK_relabel_3col σ hsub, gadgetK_3col_eq, List.length_replicate]
  rw [hgk] at hk
  have hchkL : checkGadget threeColoring (rawU own) (anchorsOf own (rawU own))
      (gadgetRows threeColoring false) (walkRawGraph tagged m base) = some k := by
    rw [← hL]
    exact hcheck.trans hk
  have hmem := searchRawAux_complete threeColoring (rawU own) (anchorsOf own (rawU own))
    (gadgetRows threeColoring false) fw (threeColoring_kill (rawU own) (anchorsOf own (rawU own))
      (gadgetRows threeColoring false)) tagged base
    { total := 2 ^ (free.length - 0) } m k hsorted hchkL
  exact ⟨σ, L, List.mem_reverse.mpr hmem, hLg⟩

/-- The negative direction: an empty canonical raw run certifies that
    `gadgetK` rejects EVERY graph of the raw slice. -/
theorem searchSliceRaw_exhaustive_threeColoring (own : Nat)
    (h : (searchSliceRaw threeColoring (List.replicate own 1)).2.found = []) :
    ∀ g ∈ (rawU own).graphs (symmetry := false)
        (forced := (threeColoring.attach (List.replicate own 1)).2),
      gadgetK threeColoring (List.replicate own 1) g false = none := by
  intro g hg
  cases hk : gadgetK threeColoring (List.replicate own 1) g false with
  | none => rfl
  | some k =>
    exfalso
    obtain ⟨_, L, hmem, _⟩ := searchSliceRaw_complete_threeColoring own g hg k hk
    rw [h] at hmem
    cases hmem

end Atlas
