import atlas.ProofsMulti
import atlas.ProofsGlue
import atlas.ProofsDecide
/-!
  P6-2 (3-coloring half): the per-problem obligations of the formula
  level, discharged for `threeColoring`, and the endpoint.

  The row instance's pin list (`rowPinsM`), the pin correspondence
  between a clause copy and the local gadget row (via the explicit
  inverse `unmapVertex` of the copy placement -- `negLayer = none`
  scope), the local eight-row table read back from `gadgetK`
  (`gadget_row_eq`), the copy transfer (`copy_colorable_eq`), the row
  semantics (`colorsOk_rowInstM_eq`), and the endpoints: for any gadget
  `g` inside the universe that passes the raw eight-row table and any
  well-formed formula ([opus5.5 review] hypotheses stated),
  `multiK threeColoring parts g clauses = some 1`
  iff the formula is satisfiable (`multiK_threeColoring_iff`), and its
  trident instance.
-/

namespace Atlas

open List

-- ------------------------------------------------------------ small kit

theorem normM_swap (e : MEdge) : normM e = e ∨ normM e = (e.2, e.1) := by
  unfold normM
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem colorAt_eq_none {β : Type} [BEq β] {pins : List (β × Nat)} {u : β}
    (h : ∀ p ∈ pins, (p.1 == u) = false) : colorAt pins u = none := by
  unfold colorAt
  rw [List.find?_eq_none.mpr fun x hx => by simp [h x hx]]
  rfl

theorem attach_size_appended (parts : List Nat) {p : Nat}
    (h1 : parts.length ≤ p)
    (h2 : p < (threeColoring.attach parts).1.parts.length) :
    (threeColoring.attach parts).1.size p = 1 := by
  have hlen : (threeColoring.attach parts).1.parts.length
      = parts.length + 3 := by
    rw [attach_parts, List.length_append]
    rfl
  have hd : p - parts.length < 3 := by omega
  have hs := attach_size parts hd
  have hop : parts.length + (p - parts.length) = p := by omega
  rw [hop] at hs
  exact hs

theorem threeColoring_negLayer : threeColoring.negLayer = none := rfl

-- --------------------------------------------- the multi-row pin list

/-- The pin list `colorsOk` builds for the multiK row at `env`. -/
def rowPinsM (clauses : List ClauseSpec) (env : Nat) : List (MVertex × Nat) :=
  [(MVertex.anchor 0, 0), (.anchor 1, 1), (.anchor 2, 2)]
    ++ ((List.range (varCount clauses)).map fun v =>
        if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v).map ((·, 0))
    ++ ((List.range (varCount clauses)).map fun v =>
        if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v).map ((·, 1))

theorem colorsOk_rowInstM (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) (env : Nat) :
    colorsOk (rowInstM threeColoring parts g clauses env)
      = colorable (assemble threeColoring parts g clauses).2
          (assemble threeColoring parts g clauses).1 (rowPinsM clauses env) := by
  have h3 : (threeColoring.attach parts).1.parts.length - parts.length = 3 := by
    rw [attach_parts, List.length_append]
    simp
  show colorable _ _
      ((((List.range ((threeColoring.attach parts).1.parts.length
            - parts.length)).map MVertex.anchor).zip [0, 1, 2])
        ++ ((List.range (varCount clauses)).map fun v =>
            if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v).map ((·, 0))
        ++ ((List.range (varCount clauses)).map fun v =>
            if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v).map ((·, 1)))
    = _
  rw [h3]
  rfl

/-- The shape of the multi-row pin keys: anchors and literal-layer
    vertices only. -/
theorem rowPinsM_keys_shape {clauses : List ClauseSpec} {env : Nat}
    {q : MVertex × Nat} (hq : q ∈ rowPinsM clauses env) :
    (∃ d, q.1 = .anchor d) ∨ ∃ v, q.1 = .pos v ∨ q.1 = .neg v := by
  unfold rowPinsM at hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl ⟨0, rfl⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl ⟨1, rfl⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl ⟨2, rfl⟩
      · exact absurd hq List.not_mem_nil
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
      by_cases hb : (env >>> v &&& 1 == 1) = true
      · exact Or.inr ⟨v, Or.inl (if_pos hb)⟩
      · exact Or.inr ⟨v, Or.inr (if_neg hb)⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
    by_cases hb : (env >>> v &&& 1 == 1) = true
    · exact Or.inr ⟨v, Or.inr (if_pos hb)⟩
    · exact Or.inr ⟨v, Or.inl (if_neg hb)⟩

theorem rowPinsM_keys_nodup (clauses : List ClauseSpec) (env : Nat) :
    ((rowPinsM clauses env).map (·.1)).Nodup := by
  unfold rowPinsM
  rw [List.map_append, List.map_append, map_fst_map_pair, map_fst_map_pair]
  have hsel : ((List.range (varCount clauses)).map fun v =>
      if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v).Nodup := by
    refine List.nodup_range.map_on ?_
    intro x _ y _ hxy
    by_cases hx : (env >>> x &&& 1 == 1) = true <;>
      by_cases hy : (env >>> y &&& 1 == 1) = true
    · rw [if_pos hx, if_pos hy] at hxy
      exact MVertex.pos.inj hxy
    · rw [if_pos hx, if_neg hy] at hxy
      cases hxy
    · rw [if_neg hx, if_pos hy] at hxy
      cases hxy
    · rw [if_neg hx, if_neg hy] at hxy
      exact MVertex.neg.inj hxy
  have hforb : ((List.range (varCount clauses)).map fun v =>
      if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v).Nodup := by
    refine List.nodup_range.map_on ?_
    intro x _ y _ hxy
    by_cases hx : (env >>> x &&& 1 == 1) = true <;>
      by_cases hy : (env >>> y &&& 1 == 1) = true
    · rw [if_pos hx, if_pos hy] at hxy
      exact MVertex.neg.inj hxy
    · rw [if_pos hx, if_neg hy] at hxy
      cases hxy
    · rw [if_neg hx, if_pos hy] at hxy
      cases hxy
    · rw [if_neg hx, if_neg hy] at hxy
      exact MVertex.pos.inj hxy
  have hanchor : ([MVertex.anchor 0, .anchor 1, .anchor 2] : List MVertex).Nodup := by
    decide
  have hanch_ne : ∀ v d : Nat,
      (if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v) = .anchor d →
      False := by
    intro v d h
    by_cases hb : (env >>> v &&& 1 == 1) = true
    · rw [if_pos hb] at h
      cases h
    · rw [if_neg hb] at h
      cases h
  have hanch_ne' : ∀ v d : Nat,
      (if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v) = .anchor d →
      False := by
    intro v d h
    by_cases hb : (env >>> v &&& 1 == 1) = true
    · rw [if_pos hb] at h
      cases h
    · rw [if_neg hb] at h
      cases h
  refine (hanchor.append hsel ?_).append hforb ?_
  · intro x hx hy
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_cons.mp hx with h | hx
    · exact hanch_ne v 0 h
    rcases List.mem_cons.mp hx with h | hx
    · exact hanch_ne v 1 h
    rcases List.mem_cons.mp hx with h | hx
    · exact hanch_ne v 2 h
    · exact absurd hx List.not_mem_nil
  · intro x hx hy
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with h | hx
      · exact hanch_ne' v 0 h
      rcases List.mem_cons.mp hx with h | hx
      · exact hanch_ne' v 1 h
      rcases List.mem_cons.mp hx with h | hx
      · exact hanch_ne' v 2 h
      · exact absurd hx List.not_mem_nil
    · obtain ⟨w, _, hw⟩ := List.mem_map.mp hx
      by_cases hbw : (env >>> w &&& 1 == 1) = true <;>
        by_cases hbv : (env >>> v &&& 1 == 1) = true
      · rw [if_pos hbw, if_pos hbv] at hw
        cases hw
      · rw [if_pos hbw, if_neg hbv] at hw
        exact hbv ((MVertex.pos.inj hw) ▸ hbw)
      · rw [if_neg hbw, if_pos hbv] at hw
        exact hbw ((MVertex.neg.inj hw).symm ▸ hbv)
      · rw [if_neg hbw, if_neg hbv] at hw
        cases hw

-- ------------------------------------------ pin values, multi-row side

theorem colorAt_rowPinsM_anchor (clauses : List ClauseSpec) (env : Nat)
    {d : Nat} (hd : d < 3) :
    colorAt (rowPinsM clauses env) (MVertex.anchor d) = some d := by
  refine colorAt_eq_some_of_mem (rowPinsM_keys_nodup clauses env) ?_
  unfold rowPinsM
  interval_cases d
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_self ..))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem colorAt_rowPinsM_lit (clauses : List ClauseSpec) (env : Nat)
    {l : Nat × Bool} (hl : l.1 < varCount clauses) :
    colorAt (rowPinsM clauses env) (litVertex l)
      = some (if litSat env l then 0 else 1) := by
  refine colorAt_eq_some_of_mem (rowPinsM_keys_nodup clauses env) ?_
  unfold rowPinsM
  obtain ⟨v, pol⟩ := l
  have hl' : v < varCount clauses := hl
  by_cases hb : (env >>> v &&& 1 == 1) = true
  · have hlit : litSat env (v, pol) = pol := by
      show ((env >>> v &&& 1 == 1) == pol) = pol
      rw [hb]
      cases pol <;> rfl
    rw [hlit]
    cases pol
    · refine List.mem_append_right _
        (List.mem_map.mpr ⟨MVertex.neg v, ?_, rfl⟩)
      exact List.mem_map.mpr ⟨v, List.mem_range.mpr hl', if_pos hb⟩
    · refine List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨MVertex.pos v, ?_, rfl⟩))
      exact List.mem_map.mpr ⟨v, List.mem_range.mpr hl', if_pos hb⟩
  · have hbf : (env >>> v &&& 1 == 1) = false := Bool.of_not_eq_true hb
    have hlit : litSat env (v, pol) = !pol := by
      show ((env >>> v &&& 1 == 1) == pol) = !pol
      rw [hbf]
      cases pol <;> rfl
    rw [hlit]
    cases pol
    · refine List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨MVertex.neg v, ?_, rfl⟩))
      exact List.mem_map.mpr ⟨v, List.mem_range.mpr hl', if_neg hb⟩
    · refine List.mem_append_right _
        (List.mem_map.mpr ⟨MVertex.pos v, ?_, rfl⟩)
      exact List.mem_map.mpr ⟨v, List.mem_range.mpr hl', if_neg hb⟩

theorem colorAt_rowPinsM_aux (clauses : List ClauseSpec) (env : Nat)
    (c p j : Nat) :
    colorAt (rowPinsM clauses env) (MVertex.aux c p j) = none := by
  refine colorAt_eq_none fun q hq => ?_
  rcases rowPinsM_keys_shape hq with ⟨d, hd⟩ | ⟨v, hv | hv⟩
  · rw [hd]
    rfl
  · rw [hv]
    rfl
  · rw [hv]
    rfl

-- ------------------------------------------ pin values, local-row side

theorem colorAt_rowPins_anchor (parts : List Nat) (env' : Nat) {d : Nat}
    (hd : d < 3) :
    colorAt (rowPins parts env') (Vertex.aux (parts.length + d) 0)
      = some d := by
  refine colorAt_eq_some_of_mem (rowPins_keys_nodup parts env') ?_
  rw [rowPins_eq]
  interval_cases d
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_self ..))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem colorAt_rowPins_lit (parts : List Nat) (env' : Nat) {i : Nat}
    (hi : i < 3) :
    colorAt (rowPins parts env') (Vertex.lit i)
      = some (if env' >>> i &&& 1 == 1 then 0 else 1) := by
  refine colorAt_eq_some_of_mem (rowPins_keys_nodup parts env') ?_
  rw [rowPins_eq]
  by_cases hb : (env' >>> i &&& 1 == 1) = true
  · rw [if_pos hb]
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨Vertex.lit i, mem_selected.mpr ⟨i, hi, hb, rfl⟩, rfl⟩))
  · rw [if_neg hb]
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨Vertex.lit i, mem_forbidden.mpr
        ⟨i, hi, Bool.of_not_eq_true hb, rfl⟩, rfl⟩)

theorem colorAt_rowPins_auxlow (parts : List Nat) (env' : Nat) {p : Nat}
    (hp : p < parts.length) (j : Nat) :
    colorAt (rowPins parts env') (Vertex.aux p j) = none := by
  refine colorAt_eq_none fun q hq => ?_
  have hkey : q.1 ∈ (rowPins parts env').map (·.1) :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [rowPins_keys] at hkey
  have habs : ∀ p' j' : Nat, parts.length ≤ p' → q.1 = Vertex.aux p' j' →
      (q.1 == Vertex.aux p j) = false := by
    intro p' j' hp' hqe
    rw [hqe]
    by_cases hbe : (Vertex.aux p' j' == Vertex.aux p j) = true
    · obtain ⟨h1, _⟩ := Vertex.aux.inj (eq_of_beq hbe)
      omega
    · exact Bool.of_not_eq_true hbe
  rcases List.mem_append.mp hkey with hkey | hkey
  · rcases List.mem_append.mp hkey with hkey | hkey
    · rcases List.mem_cons.mp hkey with h | hkey
      · exact habs parts.length 0 (Nat.le_refl _) h
      rcases List.mem_cons.mp hkey with h | hkey
      · exact habs (parts.length + 1) 0 (by omega) h
      rcases List.mem_cons.mp hkey with h | hkey
      · exact habs (parts.length + 2) 0 (by omega) h
      · exact absurd hkey List.not_mem_nil
    · obtain ⟨i, _, _, hq1⟩ := mem_selected.mp hkey
      rw [hq1]
      rfl
  · obtain ⟨i, _, _, hq1⟩ := mem_forbidden.mp hkey
    rw [hq1]
    rfl

-- --------------------------------------------------- the explicit inverse

/-- The copy-index-independent inverse of the copy placement: it reads
    the clause's literals, not its index (negLayer-free problems).
    [opus5.5 review] was "clause-independent". -/
def unmapVertex (own : Nat) (clause : ClauseSpec) : MVertex → Vertex
  | .pos v => .lit (clause.idxOf (v, true))
  | .neg v => .lit (clause.idxOf (v, false))
  | .anchor d => .aux (own + d) 0
  | .aux _ p j => .aux p j

theorem idxOf_getD {clause : ClauseSpec} (hlen : clause.length = 3)
    (hvars : ∀ i j, i < 3 → j < 3 → i ≠ j →
      (clause.getD i (0, true)).1 ≠ (clause.getD j (0, true)).1)
    {i : Nat} (hi : i < 3) :
    clause.idxOf (clause.getD i (0, true)) = i := by
  obtain ⟨l0, l1, l2, rfl⟩ := List.length_eq_three.mp hlen
  have h01 : l0 ≠ l1 := fun h =>
    hvars 0 1 (by omega) (by omega) (by omega) (congrArg Prod.fst h)
  have h02 : l0 ≠ l2 := fun h =>
    hvars 0 2 (by omega) (by omega) (by omega) (congrArg Prod.fst h)
  have h12 : l1 ≠ l2 := fun h =>
    hvars 1 2 (by omega) (by omega) (by omega) (congrArg Prod.fst h)
  interval_cases i
  · show [l0, l1, l2].idxOf l0 = 0
    simp
  · show [l0, l1, l2].idxOf l1 = 1
    simp [h01]
  · show [l0, l1, l2].idxOf l2 = 2
    simp [h02, h12]

theorem unmap_hlr (parts : List Nat) {clause : ClauseSpec}
    (hlen : clause.length = 3)
    (hvars : ∀ i j, i < 3 → j < 3 → i ≠ j →
      (clause.getD i (0, true)).1 ≠ (clause.getD j (0, true)).1) (c : Nat) :
    ∀ v ∈ (threeColoring.attach parts).1.vertices,
      unmapVertex parts.length clause
        (mapVertex threeColoring parts.length c clause v) = v := by
  intro v hv
  rcases mem_vertices.mp hv with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩
  · rw [mapVertex_lit]
    have hidx := idxOf_getD hlen hvars hi
    rcases hl : clause.getD i (0, true) with ⟨var, pol⟩
    rw [hl] at hidx
    cases pol
    · show Vertex.lit (clause.idxOf (var, false)) = Vertex.lit i
      rw [hidx]
    · show Vertex.lit (clause.idxOf (var, true)) = Vertex.lit i
      rw [hidx]
  · by_cases hpo : parts.length ≤ p
    · rw [mapVertex_anchor threeColoring c clause j hpo]
      show Vertex.aux (parts.length + (p - parts.length)) 0 = Vertex.aux p j
      have hop : parts.length + (p - parts.length) = p := by omega
      have hsz := attach_size_appended parts hpo hp
      have hj0 : j = 0 := by omega
      rw [hop, hj0]
    · rw [mapVertex_aux threeColoring c clause j hpo
        (by rw [threeColoring_negLayer]; exact fun hc => nomatch hc)]
      rfl

-- ----------------------------------------------- the local table, read back

/-- Reading the local eight-row table back from a passing `gadgetK`:
    a row is colorable exactly when its assignment is satisfiable. -/
theorem gadget_row_eq (parts : List Nat) {g : List Edge}
    (hgk : gadgetK threeColoring parts g false = some 1) :
    ∀ env', env' < 8 → colorsOk (rowInst parts g env') = (env' != 0) := by
  intro env' henv'
  rw [gadgetK_3col_eq, checkGadget_rows_eq,
    show gadgetEnvs false = List.range 8 from rfl,
    commonK_eq_some_iff] at hgk
  obtain ⟨_, hall⟩ := hgk
  have h := hall _ (List.mem_map.mpr ⟨env', List.mem_range.mpr henv', rfl⟩)
  unfold rowCond at h
  simp only [threeColoring, feasibility] at h ⊢
  cases hco : colorsOk (rowInst parts g env') <;>
    cases he : (env' != 0) <;>
      simp only [hco, he] at h <;> simp_all

-- ------------------------------------------------------ the clause copies

/-- Clause `c`'s copy of the local gadget, as it appears in `assemble`. -/
def copyM (parts : List Nat) (clauses : List ClauseSpec) (g : List Edge)
    (c : Nat) : List MEdge :=
  g.map fun e' => normM
    (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
     mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)

theorem tc_negLayer_ne (p : Nat) : threeColoring.negLayer ≠ some p := by
  rw [threeColoring_negLayer]
  exact fun hc => nomatch hc

/-- Every vertex a copy touches is the image of a universe vertex. -/
theorem copyM_touched_shape (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (clauses : List ClauseSpec) (c : Nat) :
    ∀ u : MVertex, touches (copyM parts clauses g c) u →
      ∃ v ∈ (threeColoring.attach parts).1.vertices,
        u = mapVertex threeColoring parts.length c (clauses.getD c []) v := by
  rintro u ⟨w, hw⟩
  have hdec : ∃ e' ∈ g,
      u = mapVertex threeColoring parts.length c (clauses.getD c []) e'.1 ∨
      u = mapVertex threeColoring parts.length c (clauses.getD c []) e'.2 := by
    rcases mem_adjTo.mp hw with h | h <;>
      obtain ⟨e', he', heq⟩ := List.mem_map.mp h
    · rcases normM_swap
        (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
         mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)
        with hs | hs <;> rw [hs] at heq
      · exact ⟨e', he', Or.inl (congrArg Prod.fst heq).symm⟩
      · exact ⟨e', he', Or.inr (congrArg Prod.fst heq).symm⟩
    · rcases normM_swap
        (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
         mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)
        with hs | hs <;> rw [hs] at heq
      · exact ⟨e', he', Or.inr (congrArg Prod.snd heq).symm⟩
      · exact ⟨e', he', Or.inl (congrArg Prod.snd heq).symm⟩
  obtain ⟨e', he', hu | hu⟩ := hdec
  · exact ⟨e'.1, (mem_edges (hsub e' he')).1, hu⟩
  · exact ⟨e'.2, (mem_edges (hsub e' he')).2.1, hu⟩

theorem copyM_ne (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    {clauses : List ClauseSpec} {c : Nat}
    (hlen3 : (clauses.getD c []).length = 3)
    (hvars : ∀ i j, i < 3 → j < 3 → i ≠ j →
      ((clauses.getD c []).getD i (0, true)).1
        ≠ ((clauses.getD c []).getD j (0, true)).1) :
    ∀ e ∈ copyM parts clauses g c, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  have hlr := unmap_hlr parts hlen3 hvars c
  have h1m := (mem_edges (hsub e' he')).1
  have h2m := (mem_edges (hsub e' he')).2.1
  have hne' := edges_ne (hsub e' he')
  have hσne : mapVertex threeColoring parts.length c (clauses.getD c []) e'.1
      ≠ mapVertex threeColoring parts.length c (clauses.getD c []) e'.2 :=
    fun hh => hne' (by rw [← hlr e'.1 h1m, hh, hlr e'.2 h2m])
  rcases normM_swap
      (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
       mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)
      with hs | hs <;> rw [hs]
  · exact hσne
  · exact fun hc' => hσne hc'.symm

-- ---------------------------------------------- pin correspondence, pointwise

theorem rowPins_pointwise (parts : List Nat) {clauses : List ClauseSpec}
    {c : Nat} (hc : c < clauses.length)
    (hlen3 : (clauses.getD c []).length = 3) (env : Nat) :
    ∀ v ∈ (threeColoring.attach parts).1.vertices,
      colorAt (rowPins parts (envOf (clauses.getD c []) env)) v
        = colorAt (rowPinsM clauses env)
            (mapVertex threeColoring parts.length c (clauses.getD c []) v) := by
  intro v hv
  rcases mem_vertices.mp hv with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩
  · rw [mapVertex_lit, colorAt_rowPins_lit parts _ hi]
    have hvar : ((clauses.getD c []).getD i (0, true)).1 < varCount clauses :=
      varCount_bound (getD_mem_of_lt [] hc)
        (getD_mem_of_lt (0, true) (by rw [hlen3]; exact hi))
    rw [colorAt_rowPinsM_lit clauses env hvar,
      envOf_bit (clauses.getD c []) env i hi]
  · by_cases hpo : parts.length ≤ p
    · have hlenU : (threeColoring.attach parts).1.parts.length
          = parts.length + 3 := by
        rw [attach_parts, List.length_append]
        rfl
      have hd : p - parts.length < 3 := by omega
      have hop : parts.length + (p - parts.length) = p := by omega
      have hsz := attach_size_appended parts hpo hp
      have hj0 : j = 0 := by omega
      rw [mapVertex_anchor threeColoring c _ j hpo, hj0,
        colorAt_rowPinsM_anchor clauses env hd]
      have h := colorAt_rowPins_anchor parts
        (envOf (clauses.getD c []) env) hd
      rw [hop] at h
      exact h
    · rw [mapVertex_aux threeColoring c _ j hpo (tc_negLayer_ne p),
        colorAt_rowPins_auxlow parts _ (by omega) j,
        colorAt_rowPinsM_aux]

-- ------------------------------------------------------- the copy transfer

theorem copy_colorable_eq (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    {clauses : List ClauseSpec} (hwf : WfClauses clauses) {c : Nat}
    (hc : c < clauses.length) (env : Nat) :
    colorable (copyM parts clauses g c)
        (assemble threeColoring parts g clauses).1 (rowPinsM clauses env)
      = colorable g (threeColoring.attach parts).1.vertices
          (rowPins parts (envOf (clauses.getD c []) env)) := by
  obtain ⟨hlen3, hvars⟩ := hwf (clauses.getD c []) (getD_mem_of_lt [] hc)
  have hlr := unmap_hlr parts hlen3 hvars c
  have hedges : ∀ e ∈ g,
      e.1 ∈ (threeColoring.attach parts).1.vertices ∧
      e.2 ∈ (threeColoring.attach parts).1.vertices := fun e he =>
    ⟨(mem_edges (hsub e he)).1, (mem_edges (hsub e he)).2.1⟩
  have hne : ∀ e ∈ g, e.1 ≠ e.2 := fun e he => edges_ne (hsub e he)
  have hnd := vertices_nodup (threeColoring.attach parts).1
  have hkeys : ∀ q ∈ rowPins parts (envOf (clauses.getD c []) env),
      q.1 ∈ (threeColoring.attach parts).1.vertices := fun q hq =>
    rowPins_keys_mem parts _ q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
  -- step 1: rename along the copy placement
  have h1 := colorable_rename
    (σ := mapVertex threeColoring parts.length c (clauses.getD c []))
    (σ' := unmapVertex parts.length (clauses.getD c [])) hlr g
    (threeColoring.attach parts).1.vertices
    (rowPins parts (envOf (clauses.getD c []) env)) hedges hne
    (fun _ hv => hv) hkeys hnd
  -- loop-freeness of the mapped pair list and of the copy
  have hloopPair : ∀ a : MVertex, a ∉ adjTo (g.map fun e' =>
      (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
       mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)) a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h
    · obtain ⟨e', he', heq⟩ := List.mem_map.mp h
      have hf : mapVertex threeColoring parts.length c (clauses.getD c []) e'.1
          = a := congrArg Prod.fst heq
      have hs : mapVertex threeColoring parts.length c (clauses.getD c []) e'.2
          = a := congrArg Prod.snd heq
      exact hne e' he' (by
        rw [← hlr e'.1 (hedges e' he').1, ← hlr e'.2 (hedges e' he').2, hf, hs])
    · obtain ⟨e', he', heq⟩ := List.mem_map.mp h
      have hf : mapVertex threeColoring parts.length c (clauses.getD c []) e'.1
          = a := congrArg Prod.fst heq
      have hs : mapVertex threeColoring parts.length c (clauses.getD c []) e'.2
          = a := congrArg Prod.snd heq
      exact hne e' he' (by
        rw [← hlr e'.1 (hedges e' he').1, ← hlr e'.2 (hedges e' he').2, hf, hs])
  -- step 2: normalization is adjacency-free
  have hmm : (g.map fun e' =>
      (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
       mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)).map
        normM = copyM parts clauses g c := by
    rw [List.map_map]
    rfl
  have h2 : ∀ v u : MVertex, u ∈ adjTo (copyM parts clauses g c) v ↔
      u ∈ adjTo (g.map fun e' =>
        (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
         mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)) v := by
    intro v u
    rw [← hmm]
    exact adjTo_map_swap normM_swap _ v u
  have hloopCopy : ∀ a : MVertex, a ∉ adjTo (copyM parts clauses g c) a :=
    fun a ha => hloopPair a ((h2 a a).mp ha)
  have hndmap : ((threeColoring.attach parts).1.vertices.map
      (mapVertex threeColoring parts.length c (clauses.getD c []))).Nodup :=
    hnd.map_on fun x hx y hy hxy => by
      rw [← hlr x hx, hxy, hlr y hy]
  have h2' := colorable_congr_edges
    ((threeColoring.attach parts).1.vertices.map
      (mapVertex threeColoring parts.length c (clauses.getD c [])))
    ((rowPins parts (envOf (clauses.getD c []) env)).map fun q =>
      (mapVertex threeColoring parts.length c (clauses.getD c []) q.1, q.2))
    hloopPair hndmap (fun v u => ((h2 v u).symm))
  -- step 3: the pins agree on the mapped carrier
  have h3 := colorable_congr_pins_mem (copyM parts clauses g c)
    ((threeColoring.attach parts).1.vertices.map
      (mapVertex threeColoring parts.length c (clauses.getD c [])))
    (pins₁ := (rowPins parts (envOf (clauses.getD c []) env)).map fun q =>
      (mapVertex threeColoring parts.length c (clauses.getD c []) q.1, q.2))
    (pins₂ := rowPinsM clauses env)
    hloopCopy hndmap
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      rw [colorAt_map hlr hkeys hv]
      exact rowPins_pointwise parts hc hlen3 env v hv)
  -- step 4: widen the vertex list to the assembly
  have hndA : (assemble threeColoring parts g clauses).1.Nodup := by
    show ((((List.range (varCount clauses)).flatMap fun v =>
        [MVertex.pos v, MVertex.neg v])
      ++ (assemble threeColoring parts g clauses).2.flatMap fun e =>
        [e.1, e.2]).eraseDups).Nodup
    exact nodup_eraseDups _
  have h4 := colorable_congr_verts_touched (copyM parts clauses g c)
    (rowPinsM clauses env) hloopCopy hndmap hndA
    (by
      intro u ht
      obtain ⟨v, hv, rfl⟩ := copyM_touched_shape parts hsub clauses c u ht
      have hmemE : ∀ {e' : Edge}, e' ∈ g → normM
          (mapVertex threeColoring parts.length c (clauses.getD c []) e'.1,
           mapVertex threeColoring parts.length c (clauses.getD c []) e'.2)
          ∈ (assemble threeColoring parts g clauses).2 := by
        intro e' he'
        refine (mem_assemble_edges threeColoring parts g clauses).mpr
          ⟨Or.inl ⟨c, hc, e', he', rfl⟩, ?_⟩
        exact copyM_ne parts hsub hlen3 hvars _
          (List.mem_map.mpr ⟨e', he', rfl⟩)
      constructor
      · intro _
        obtain ⟨w, hw⟩ := ht
        rcases mem_adjTo.mp hw with h | h
        · obtain ⟨e', he', heq⟩ := List.mem_map.mp h
          exact (mem_assemble_verts threeColoring parts g clauses).mpr
            (Or.inr ⟨_, hmemE he', Or.inl (congrArg Prod.fst heq).symm⟩)
        · obtain ⟨e', he', heq⟩ := List.mem_map.mp h
          exact (mem_assemble_verts threeColoring parts g clauses).mpr
            (Or.inr ⟨_, hmemE he', Or.inr (congrArg Prod.snd heq).symm⟩)
      · intro _
        exact List.mem_map.mpr ⟨v, hv, rfl⟩)
  rw [h4] at h3
  rw [h3] at h2'
  rw [h2'] at h1
  exact h1

-- -------------------------------------------------- the layer, pinned

theorem mem_threeColoring_layer {n : Nat} {w : MEdge} :
    w ∈ threeColoring.layer n ↔ ∃ v, v < n ∧
      (w = (.pos v, .neg v) ∨ w = (.pos v, .anchor 2) ∨
       w = (.neg v, .anchor 2)) := by
  show w ∈ (List.range n).flatMap (fun v =>
    [(MVertex.pos v, MVertex.neg v), (.pos v, .anchor 2),
     (.neg v, .anchor 2)]) ↔ _
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨v, hv, hmem⟩
    refine ⟨v, List.mem_range.mp hv, ?_⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inl rfl
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inr (Or.inl rfl)
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inr (Or.inr rfl)
    · exact absurd hmem List.not_mem_nil
  · rintro ⟨v, hv, rfl | rfl | rfl⟩
    · exact ⟨v, List.mem_range.mpr hv, List.mem_cons_self ..⟩
    · exact ⟨v, List.mem_range.mpr hv,
        List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
    · exact ⟨v, List.mem_range.mpr hv, List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

theorem layer_edge_ne {n : Nat} {w : MEdge}
    (hw : w ∈ threeColoring.layer n) : w.1 ≠ w.2 := by
  obtain ⟨v, _, h | h | h⟩ := mem_threeColoring_layer.mp hw <;> rw [h] <;>
    exact fun hc => nomatch hc

theorem layer_pinned (clauses : List ClauseSpec) (env : Nat) {w : MEdge}
    (hw : w ∈ threeColoring.layer (varCount clauses)) :
    ∃ c₁ c₂, colorAt (rowPinsM clauses env) w.1 = some c₁ ∧
      colorAt (rowPinsM clauses env) w.2 = some c₂ ∧ c₁ ≠ c₂ := by
  obtain ⟨v, hv, h | h | h⟩ := mem_threeColoring_layer.mp hw
  · rw [h]
    have hp := colorAt_rowPinsM_lit clauses env (l := (v, true)) hv
    have hn := colorAt_rowPinsM_lit clauses env (l := (v, false)) hv
    refine ⟨if litSat env (v, true) then 0 else 1,
      if litSat env (v, false) then 0 else 1, hp, hn, ?_⟩
    have hop : litSat env (v, true) = !litSat env (v, false) := by
      show ((env >>> v &&& 1 == 1) == true) = !((env >>> v &&& 1 == 1) == false)
      cases env >>> v &&& 1 == 1 <;> rfl
    rw [hop]
    cases litSat env (v, false) <;> decide
  · rw [h]
    have hp := colorAt_rowPinsM_lit clauses env (l := (v, true)) hv
    have ha := colorAt_rowPinsM_anchor clauses env (d := 2) (by omega)
    refine ⟨if litSat env (v, true) then 0 else 1, 2, hp, ha, ?_⟩
    cases litSat env (v, true) <;> decide
  · rw [h]
    have hp := colorAt_rowPinsM_lit clauses env (l := (v, false)) hv
    have ha := colorAt_rowPinsM_anchor clauses env (d := 2) (by omega)
    refine ⟨if litSat env (v, false) then 0 else 1, 2, hp, ha, ?_⟩
    cases litSat env (v, false) <;> decide

theorem layerM_ne {n : Nat} :
    ∀ e ∈ (threeColoring.layer n).map normM, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
  have hne := layer_edge_ne hw
  rcases normM_swap w with hs | hs <;> rw [hs]
  · exact hne
  · exact fun hc' => hne hc'.symm

theorem layerM_pinned (clauses : List ClauseSpec) (env : Nat) :
    ∀ e ∈ (threeColoring.layer (varCount clauses)).map normM,
      ∃ c₁ c₂, colorAt (rowPinsM clauses env) e.1 = some c₁ ∧
        colorAt (rowPinsM clauses env) e.2 = some c₂ ∧ c₁ ≠ c₂ := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
  obtain ⟨c₁, c₂, h1, h2, hne⟩ := layer_pinned clauses env hw
  rcases normM_swap w with hs | hs <;> rw [hs]
  · exact ⟨c₁, c₂, h1, h2, hne⟩
  · exact ⟨c₂, c₁, h2, h1, fun h => hne h.symm⟩

theorem layerM_touched_pinned (clauses : List ClauseSpec) (env : Nat) :
    ∀ u : MVertex,
      touches ((threeColoring.layer (varCount clauses)).map normM) u →
      (colorAt (rowPinsM clauses env) u).isSome = true := by
  rintro u ⟨w', hw'⟩
  have hend : ∀ {e : MEdge},
      e ∈ (threeColoring.layer (varCount clauses)).map normM →
      (u = e.1 ∨ u = e.2) → (colorAt (rowPinsM clauses env) u).isSome = true := by
    intro e he hu
    obtain ⟨c₁, c₂, h1, h2, _⟩ := layerM_pinned clauses env e he
    rcases hu with rfl | rfl
    · rw [h1]
      rfl
    · rw [h2]
      rfl
  rcases mem_adjTo.mp hw' with h | h
  · exact hend h (Or.inl rfl)
  · exact hend h (Or.inr rfl)

-- ------------------------------------- the assembly as glued components

def partsListM (parts : List Nat) (clauses : List ClauseSpec)
    (g : List Edge) : List (List MEdge) :=
  ((threeColoring.layer (varCount clauses)).map normM)
    :: (List.range clauses.length).map (copyM parts clauses g)

theorem assemble_mem_flatten (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    {clauses : List ClauseSpec} (hwf : WfClauses clauses) (e : MEdge) :
    e ∈ (assemble threeColoring parts g clauses).2 ↔
      e ∈ (partsListM parts clauses g).flatten := by
  rw [mem_assemble_edges]
  unfold partsListM
  rw [List.flatten_cons, List.mem_append]
  constructor
  · rintro ⟨hform, hne⟩
    rcases hform with ⟨c, hc, e', he', rfl⟩ | ⟨w, hw, rfl⟩
    · refine Or.inr (List.mem_flatten.mpr
        ⟨copyM parts clauses g c, List.mem_map.mpr
          ⟨c, List.mem_range.mpr hc, rfl⟩, List.mem_map.mpr ⟨e', he', rfl⟩⟩)
    · exact Or.inl (List.mem_map.mpr ⟨w, hw, rfl⟩)
  · rintro (h | h)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      exact ⟨Or.inr ⟨w, hw, rfl⟩, layerM_ne _ (List.mem_map.mpr ⟨w, hw, rfl⟩)⟩
    · obtain ⟨L, hL, heL⟩ := List.mem_flatten.mp h
      obtain ⟨c, hcr, rfl⟩ := List.mem_map.mp hL
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp heL
      have hc := List.mem_range.mp hcr
      obtain ⟨hlen3, hvars⟩ := hwf _ (getD_mem_of_lt [] hc)
      refine ⟨Or.inl ⟨c, hc, e', he', rfl⟩, ?_⟩
      exact copyM_ne parts hsub hlen3 hvars _ (List.mem_map.mpr ⟨e', he', rfl⟩)

theorem copies_shared (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    {clauses : List ClauseSpec} (hwf : WfClauses clauses) (env : Nat)
    {c c' : Nat} (hc : c < clauses.length) (hcc : c ≠ c') :
    ∀ u : MVertex, touches (copyM parts clauses g c) u →
      touches (copyM parts clauses g c') u →
      (colorAt (rowPinsM clauses env) u).isSome = true := by
  intro u ht ht'
  obtain ⟨v, hv, rfl⟩ := copyM_touched_shape parts hsub clauses c u ht
  rcases mem_vertices.mp hv with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩
  · rw [mapVertex_lit]
    have hvar : ((clauses.getD c []).getD i (0, true)).1 < varCount clauses := by
      obtain ⟨hlen3, _⟩ := hwf _ (getD_mem_of_lt [] hc)
      exact varCount_bound (getD_mem_of_lt [] hc)
        (getD_mem_of_lt (0, true) (by rw [hlen3]; exact hi))
    rw [colorAt_rowPinsM_lit clauses env hvar]
    rfl
  · by_cases hpo : parts.length ≤ p
    · have hlenU : (threeColoring.attach parts).1.parts.length
          = parts.length + 3 := by
        rw [attach_parts, List.length_append]
        rfl
      have hd : p - parts.length < 3 := by omega
      rw [mapVertex_anchor threeColoring c _ j hpo,
        colorAt_rowPinsM_anchor clauses env hd]
      rfl
    · exfalso
      rw [mapVertex_aux threeColoring c _ j hpo (tc_negLayer_ne p)] at ht'
      obtain ⟨v', hv', hv'e⟩ :=
        copyM_touched_shape parts hsub clauses c' _ ht'
      rcases mem_vertices.mp hv' with ⟨i', hi', rfl⟩ | ⟨p', j', hp', hj', rfl⟩
      · rw [mapVertex_lit] at hv'e
        exact litVertex_ne_aux _ _ _ _ hv'e.symm
      · by_cases hpo' : parts.length ≤ p'
        · rw [mapVertex_anchor threeColoring c' _ j' hpo'] at hv'e
          cases hv'e
        · rw [mapVertex_aux threeColoring c' _ j' hpo'
            (tc_negLayer_ne p')] at hv'e
          exact hcc (MVertex.aux.inj hv'e).1

-- ------------------------------------------------------ the row semantics

/-- The 3-coloring obligation of the feasibility aggregation: a multiK
    row is colorable exactly when the formula row is satisfied -- for
    any local gadget passing the raw eight-row table. -/
theorem colorsOk_rowInstM_eq (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hgk : gadgetK threeColoring parts g false = some 1)
    {clauses : List ClauseSpec} (hwf : WfClauses clauses) (env : Nat) :
    colorsOk (rowInstM threeColoring parts g clauses env)
      = formulaSat env clauses := by
  rw [colorsOk_rowInstM]
  have hndA : (assemble threeColoring parts g clauses).1.Nodup := by
    show ((((List.range (varCount clauses)).flatMap fun v =>
        [MVertex.pos v, MVertex.neg v])
      ++ (assemble threeColoring parts g clauses).2.flatMap fun e =>
        [e.1, e.2]).eraseDups).Nodup
    exact nodup_eraseDups _
  have hloopA : ∀ a : MVertex,
      a ∉ adjTo (assemble threeColoring parts g clauses).2 a := by
    intro a ha
    rcases mem_adjTo.mp ha with h | h <;>
      exact ((mem_assemble_edges threeColoring parts g clauses).mp h).2 rfl
  rw [colorable_congr_edges (assemble threeColoring parts g clauses).1
    (rowPinsM clauses env) hloopA hndA
    (adjTo_congr_mem (assemble_mem_flatten parts hsub hwf))]
  have hloopParts : ∀ E ∈ partsListM parts clauses g, ∀ a : MVertex,
      a ∉ adjTo E a := by
    intro E hE
    unfold partsListM at hE
    rcases List.mem_cons.mp hE with rfl | hE
    · intro a ha
      rcases mem_adjTo.mp ha with h | h <;> exact layerM_ne _ h rfl
    · obtain ⟨c, hcr, rfl⟩ := List.mem_map.mp hE
      have hc := List.mem_range.mp hcr
      obtain ⟨hlen3, hvars⟩ := hwf _ (getD_mem_of_lt [] hc)
      intro a ha
      rcases mem_adjTo.mp ha with h | h <;>
        exact copyM_ne parts hsub hlen3 hvars _ h rfl
  have hshared : (partsListM parts clauses g).Pairwise fun E E' =>
      ∀ v : MVertex, touches E v → touches E' v →
        (colorAt (rowPinsM clauses env) v).isSome = true := by
    unfold partsListM
    rw [List.pairwise_cons]
    constructor
    · intro E' _ v ht _
      exact layerM_touched_pinned clauses env v ht
    · rw [List.pairwise_map]
      refine pairwise_strengthen List.nodup_range ?_
      intro c hcr c' _ hcc v ht ht'
      exact copies_shared parts hsub hwf env (List.mem_range.mp hcr) hcc
        v ht ht'
  rw [colorable_glue (partsListM parts clauses g)
    (assemble threeColoring parts g clauses).1 (rowPinsM clauses env)
    hloopParts hndA hshared]
  unfold partsListM
  rw [List.all_cons]
  show (colorable ((threeColoring.layer (varCount clauses)).map normM)
      (assemble threeColoring parts g clauses).1 (rowPinsM clauses env)
    && ((List.range clauses.length).map (copyM parts clauses g)).all
      (fun E => colorable E (assemble threeColoring parts g clauses).1
        (rowPinsM clauses env))) = _
  rw [colorable_of_pinned_edges
    ((threeColoring.layer (varCount clauses)).map normM)
    (assemble threeColoring parts g clauses).1 (rowPinsM clauses env)
    (by
      intro a ha
      rcases mem_adjTo.mp ha with h | h <;> exact layerM_ne _ h rfl)
    hndA (layerM_pinned clauses env), Bool.true_and]
  rw [List.all_map]
  rw [all_congr'
    (p := (fun E => colorable E (assemble threeColoring parts g clauses).1
      (rowPinsM clauses env)) ∘ copyM parts clauses g)
    (q := fun c => envOf (clauses.getD c []) env != 0)
    (fun c hcr => by
      have hc := List.mem_range.mp hcr
      show colorable (copyM parts clauses g c)
        (assemble threeColoring parts g clauses).1 (rowPinsM clauses env) = _
      rw [copy_colorable_eq parts hsub hwf hc env]
      show colorsOk (rowInst parts g (envOf (clauses.getD c []) env)) = _
      exact gadget_row_eq parts hgk _ (envOf_lt _ env))]
  rw [all_range_getD [] (fun clause => envOf clause env != 0) clauses]
  exact (formulaSat_eq_all_envOf (fun cl hcl => (hwf cl hcl).1) env).symm

-- ------------------------------------------------------------ endpoints

/-- P6-2 headline: for any local gadget that passes the raw eight-row
    table and any well-formed formula, the assembled graph's table reads
    budget 1 exactly when the formula is satisfiable. -/
theorem multiK_threeColoring_iff (parts : List Nat) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges)
    (hgk : gadgetK threeColoring parts g false = some 1)
    {clauses : List ClauseSpec} (hwf : WfClauses clauses) :
    (multiK threeColoring parts g clauses = some 1
      ↔ ∃ env, env < 2 ^ varCount clauses ∧ formulaSat env clauses = true) := by
  refine feasibility_multiK_iff "3-coloring" colorsOk threeColoring.attach
    threeColoring.layer threeColoring.viable parts g clauses ?_
  intro env henv
  exact colorsOk_rowInstM_eq parts hsub hgk hwf env

theorem tridentA_sub :
    ∀ e ∈ tridentA, e ∈ (threeColoring.attach [3, 3]).1.edges := by
  decide

theorem tridentA_gadgetK_raw :
    gadgetK threeColoring [3, 3] tridentA false = some 1 := by
  decide

/-- The table-level (pinned-row) statement, end to end on the sweep's own
    find ([opus5.5 review] was "The reduction"; the reduction proper is the
    pin-free form cited below): for every
    well-formed 3SAT formula, the engine's full-table verdict on the
    trident assembly reads budget 1 exactly when the formula is
    satisfiable -- every pinned row is colorable iff its assignment
    satisfies the formula. The pin-free form ("the assembled graph,
    palette pinned, is 3-colorable iff satisfiable") is
    `trident_colorable_iff` in `atlas/ProofsMultiColFree.lean`, through
    the layer-forcing lemma that any proper coloring of the assembly
    induces a row. -/
theorem trident_multiK_iff {clauses : List ClauseSpec}
    (hwf : WfClauses clauses) :
    (multiK threeColoring [3, 3] tridentA clauses = some 1
      ↔ ∃ env, env < 2 ^ varCount clauses ∧ formulaSat env clauses = true) :=
  multiK_threeColoring_iff [3, 3] tridentA_sub tridentA_gadgetK_raw hwf

end Atlas
