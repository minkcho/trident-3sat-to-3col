import Mathlib.Tactic.IntervalCases
import atlas.ProofsAction
import atlas.ProofsAssemble2
import atlas.ProofsSym
-- [opus5.5 review] contents list: `mapVertex_inj` was removed in the
-- 0902 clean-up; the file now has the literal-vertex facts and the per-arm
-- rewrites of `mapVertex`
/-!
  P6-1: the generic assembly combinatorics and the multi-clause row
  plumbing -- everything here is problem-independent (∀ P) and carries
  no per-problem obligations.

  Contents: membership characterizations of the generic assembler
  `assembleVia` (instantiated to `assemble` and `occAssemble`),
  well-formedness of 3SAT inputs (`WfClauses`), the literal-vertex facts
  `litVertex_inj`/`litVertex_ne_aux` and the per-arm rewrites of the copy
  placement `mapVertex`, the clause-local assignment `envOf` induced by a
  global assignment with its bit/`formulaSat`/`satCount` bridges, and
  the unfolding of `multiK` into `commonK` over explicit row instances
  (`rowInstM`, `multiK_rows_eq`) -- the base the kit-level aggregation
  rounds (P6-2, P6-3) stand on.
-/

namespace Atlas

open List

-- ----------------------------- the generic assembler, membership level

theorem mem_assembleVia_edges {V : Type} [BEq V] [LawfulBEq V]
    (normV : V × V → V × V) (merge : OVertex → V) (P : Problem)
    (parts : List Nat) (g : List Edge) (clauses : List ClauseSpec)
    (wiring : List (V × V)) (base : List V) {e : V × V} :
    e ∈ (assembleVia normV merge P parts g clauses wiring base).2 ↔
      ((∃ c, c < clauses.length ∧ ∃ e' ∈ g,
          e = normV (merge (occMapVertex P parts.length c e'.1),
                     merge (occMapVertex P parts.length c e'.2))) ∨
        ∃ w ∈ wiring, e = normV w) ∧ e.1 ≠ e.2 := by
  show e ∈ (((List.range clauses.length).flatMap fun c =>
        g.map fun e' => normV (merge (occMapVertex P parts.length c e'.1),
                               merge (occMapVertex P parts.length c e'.2)))
      ++ wiring.map normV).eraseDups.filter (fun e => e.1 != e.2) ↔ _
  rw [List.mem_filter, List.mem_eraseDups, List.mem_append]
  constructor
  · rintro ⟨h | h, hne⟩
    · obtain ⟨c, hc, hmem⟩ := List.mem_flatMap.mp h
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hmem
      exact ⟨Or.inl ⟨c, List.mem_range.mp hc, e', he', heq.symm⟩,
        bne_iff_ne.mp hne⟩
    · obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
      exact ⟨Or.inr ⟨w, hw, heq.symm⟩, bne_iff_ne.mp hne⟩
  · rintro ⟨h | h, hne⟩
    · obtain ⟨c, hc, e', he', rfl⟩ := h
      exact ⟨Or.inl (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc,
        List.mem_map.mpr ⟨e', he', rfl⟩⟩), bne_iff_ne.mpr hne⟩
    · obtain ⟨w, hw, rfl⟩ := h
      exact ⟨Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩), bne_iff_ne.mpr hne⟩

theorem mem_assembleVia_verts {V : Type} [BEq V] [LawfulBEq V]
    (normV : V × V → V × V) (merge : OVertex → V) (P : Problem)
    (parts : List Nat) (g : List Edge) (clauses : List ClauseSpec)
    (wiring : List (V × V)) (base : List V) {v : V} :
    v ∈ (assembleVia normV merge P parts g clauses wiring base).1 ↔
      v ∈ base ∨
      ∃ e ∈ (assembleVia normV merge P parts g clauses wiring base).2,
        v = e.1 ∨ v = e.2 := by
  show v ∈ (base ++ (assembleVia normV merge P parts g clauses wiring
      base).2.flatMap fun e => [e.1, e.2]).eraseDups ↔ _
  rw [List.mem_eraseDups, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨e, he, hmem⟩ := List.mem_flatMap.mp h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact Or.inr ⟨e, he, Or.inl rfl⟩
      rcases List.mem_cons.mp hmem' with rfl | hmem''
      · exact Or.inr ⟨e, he, Or.inr rfl⟩
      · exact absurd hmem'' List.not_mem_nil
  · rintro (h | ⟨e, he, rfl | rfl⟩)
    · exact Or.inl h
    · exact Or.inr (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_self ..⟩)
    · exact Or.inr (List.mem_flatMap.mpr
        ⟨e, he, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩)

/-- Membership in the multi-clause edge list: a clause copy of a gadget
    edge or a layer edge, never a self-loop. -/
theorem mem_assemble_edges (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) {e : MEdge} :
    e ∈ (assemble P parts g clauses).2 ↔
      ((∃ c, c < clauses.length ∧ ∃ e' ∈ g,
          e = normM (mapVertex P parts.length c (clauses.getD c []) e'.1,
                     mapVertex P parts.length c (clauses.getD c []) e'.2)) ∨
        ∃ w ∈ P.layer (varCount clauses), e = normM w) ∧ e.1 ≠ e.2 := by
  have h := mem_assembleVia_edges normM (mergeByLiteral clauses) P parts g
    clauses (P.layer (varCount clauses))
    ((List.range (varCount clauses)).flatMap fun w =>
      [MVertex.pos w, MVertex.neg w]) (e := e)
  rw [show assembleVia normM (mergeByLiteral clauses) P parts g clauses
      (P.layer (varCount clauses))
      ((List.range (varCount clauses)).flatMap fun w =>
        [MVertex.pos w, MVertex.neg w]) = assemble P parts g clauses from
    phase1Assemble_eq_assemble P parts g clauses] at h
  simpa only [mergeByLiteral_occMapVertex] using h

theorem mem_assemble_verts (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) {v : MVertex} :
    v ∈ (assemble P parts g clauses).1 ↔
      v ∈ ((List.range (varCount clauses)).flatMap fun w =>
        [MVertex.pos w, MVertex.neg w]) ∨
      ∃ e ∈ (assemble P parts g clauses).2, v = e.1 ∨ v = e.2 := by
  have h := mem_assembleVia_verts normM (mergeByLiteral clauses) P parts g
    clauses (P.layer (varCount clauses))
    ((List.range (varCount clauses)).flatMap fun w =>
      [MVertex.pos w, MVertex.neg w]) (v := v)
  rw [show assembleVia normM (mergeByLiteral clauses) P parts g clauses
      (P.layer (varCount clauses))
      ((List.range (varCount clauses)).flatMap fun w =>
        [MVertex.pos w, MVertex.neg w]) = assemble P parts g clauses from
    phase1Assemble_eq_assemble P parts g clauses] at h
  exact h

/-- A gadget edge placed in clause `c`'s copy is an edge of the assembly
    (unless it degenerates to a loop). Problem-generic; the per-problem
    `*_copy_edge_mem` lemmas are its instances. -/
theorem copy_edge_mem (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) {c : Nat} (hc : c < clauses.length)
    {e' : Edge} (he' : e' ∈ g)
    (hne : (normM (mapVertex P parts.length c (clauses.getD c []) e'.1,
        mapVertex P parts.length c (clauses.getD c []) e'.2)).1
      ≠ (normM (mapVertex P parts.length c (clauses.getD c []) e'.1,
        mapVertex P parts.length c (clauses.getD c []) e'.2)).2) :
    normM (mapVertex P parts.length c (clauses.getD c []) e'.1,
        mapVertex P parts.length c (clauses.getD c []) e'.2)
      ∈ (assemble P parts g clauses).2 :=
  (mem_assemble_edges P parts g clauses).mpr ⟨Or.inl ⟨c, hc, e', he', rfl⟩, hne⟩

theorem mem_occAssemble_edges (P : Problem) (parts : List Nat)
    (g : List Edge) (clauses : List ClauseSpec) (wiring : List OEdge)
    {e : OEdge} :
    e ∈ (occAssemble P parts g clauses wiring).2 ↔
      ((∃ c, c < clauses.length ∧ ∃ e' ∈ g,
          e = normO (occMapVertex P parts.length c e'.1,
                     occMapVertex P parts.length c e'.2)) ∨
        ∃ w ∈ wiring, e = normO w) ∧ e.1 ≠ e.2 := by
  unfold occAssemble
  have h := mem_assembleVia_edges normO id P parts g clauses wiring
    (occVerts clauses) (e := e)
  simpa only [id_eq] using h

theorem mem_occAssemble_verts (P : Problem) (parts : List Nat)
    (g : List Edge) (clauses : List ClauseSpec) (wiring : List OEdge)
    {v : OVertex} :
    v ∈ (occAssemble P parts g clauses wiring).1 ↔
      v ∈ occVerts clauses ∨
      ∃ e ∈ (occAssemble P parts g clauses wiring).2, v = e.1 ∨ v = e.2 := by
  unfold occAssemble
  exact mem_assembleVia_verts normO id P parts g clauses wiring
    (occVerts clauses)

-- ------------------------------------- well-formed inputs and injectivity

/-- Well-formed 3SAT input: every clause has exactly three literals over
    pairwise-distinct variables. -/
def WfClauses (clauses : List ClauseSpec) : Prop :=
  ∀ clause ∈ clauses, clause.length = 3 ∧
    ∀ i j, i < 3 → j < 3 → i ≠ j →
      (clause.getD i (0, true)).1 ≠ (clause.getD j (0, true)).1

theorem litVertex_inj {l l' : Nat × Bool} (h : litVertex l = litVertex l') :
    l = l' := by
  obtain ⟨v, pol⟩ := l
  obtain ⟨v', pol'⟩ := l'
  cases pol <;> cases pol' <;> simp [litVertex] at h <;> simp [h]

theorem litVertex_ne_aux (l : Nat × Bool) (c p j : Nat) :
    litVertex l ≠ .aux c p j := by
  obtain ⟨v, pol⟩ := l
  cases pol <;> simp [litVertex]

/-- Rewrite forms of `mapVertex`, one per arm. -/
theorem mapVertex_lit (P : Problem) (own c : Nat) (clause : ClauseSpec)
    (i : Nat) :
    mapVertex P own c clause (.lit i) = litVertex (clause.getD i (0, true)) :=
  rfl

theorem mapVertex_anchor (P : Problem) {own p : Nat} (c : Nat)
    (clause : ClauseSpec) (j : Nat) (hp : own ≤ p) :
    mapVertex P own c clause (.aux p j) = .anchor (p - own) := by
  show (if p ≥ own then MVertex.anchor (p - own)
    else if P.negLayer == some p then negLitVertex (clause.getD j (0, true))
    else MVertex.aux c p j) = MVertex.anchor (p - own)
  rw [if_pos hp]

theorem mapVertex_negLayer (P : Problem) {own p : Nat} (c : Nat)
    (clause : ClauseSpec) (j : Nat) (hp : ¬own ≤ p)
    (hn : P.negLayer = some p) :
    mapVertex P own c clause (.aux p j)
      = negLitVertex (clause.getD j (0, true)) := by
  show (if p ≥ own then MVertex.anchor (p - own)
    else if P.negLayer == some p then negLitVertex (clause.getD j (0, true))
    else MVertex.aux c p j) = negLitVertex (clause.getD j (0, true))
  rw [if_neg hp, if_pos (by rw [hn]; exact beq_self_eq_true _)]

theorem mapVertex_aux (P : Problem) {own p : Nat} (c : Nat)
    (clause : ClauseSpec) (j : Nat) (hp : ¬own ≤ p)
    (hn : P.negLayer ≠ some p) :
    mapVertex P own c clause (.aux p j) = .aux c p j := by
  show (if p ≥ own then MVertex.anchor (p - own)
    else if P.negLayer == some p then negLitVertex (clause.getD j (0, true))
    else MVertex.aux c p j) = MVertex.aux c p j
  rw [if_neg hp, if_neg (fun hc => hn (eq_of_beq hc))]

-- ------------------------------------------------- the induced row action

/-- The clause-local assignment induced by a global assignment: bit `i`
    is the truth of the clause's i-th literal, read with the same
    `getD` access `mapVertex` uses. -/
def envOf (clause : ClauseSpec) (env : Nat) : Nat :=
  (if litSat env (clause.getD 0 (0, true)) then 1 else 0) |||
    ((if litSat env (clause.getD 1 (0, true)) then 2 else 0) |||
      (if litSat env (clause.getD 2 (0, true)) then 4 else 0))

theorem envOf_bit (clause : ClauseSpec) (env : Nat) :
    ∀ i, i < 3 → (envOf clause env >>> i &&& 1 == 1)
      = litSat env (clause.getD i (0, true)) := by
  intro i hi
  unfold envOf
  cases h0 : litSat env (clause.getD 0 (0, true)) <;>
    cases h1 : litSat env (clause.getD 1 (0, true)) <;>
      cases h2 : litSat env (clause.getD 2 (0, true)) <;>
        interval_cases i <;> simp_all

/-- A clause is satisfied exactly when its induced local assignment is
    a satisfiable gadget row (nonzero). Needs the length-3 shape: a
    longer clause could be satisfied beyond its first three literals. -/
theorem any_litSat_eq_envOf_ne {clause : ClauseSpec}
    (hlen : clause.length = 3) (env : Nat) :
    (clause.any fun l => (env >>> l.1 &&& 1 == 1) == l.2)
      = (envOf clause env != 0) := by
  obtain ⟨l0, l1, l2, rfl⟩ := List.length_eq_three.mp hlen
  show ([l0, l1, l2].any (litSat env)) = _
  cases h0 : litSat env l0 <;> cases h1 : litSat env l1 <;>
    cases h2 : litSat env l2 <;> simp [envOf, h0, h1, h2]

theorem formulaSat_eq_all_envOf {clauses : List ClauseSpec}
    (hlen : ∀ clause ∈ clauses, clause.length = 3) (env : Nat) :
    formulaSat env clauses
      = clauses.all fun clause => envOf clause env != 0 := by
  induction clauses with
  | nil => rfl
  | cons cl rest ih =>
    show ((cl.any fun l => (env >>> l.1 &&& 1 == 1) == l.2)
        && formulaSat env rest)
      = (cl :: rest).all fun clause => envOf clause env != 0
    rw [List.all_cons,
      any_litSat_eq_envOf_ne (hlen cl (List.mem_cons_self ..)) env,
      ih fun c hc => hlen c (List.mem_cons_of_mem _ hc)]

/-- The TAT count identity: every clause satisfied ↔ the satisfied-clause
    count reaches the clause count. -/
theorem satCount_eq_length_iff (clauses : List ClauseSpec) (env : Nat) :
    satCount clauses env = clauses.length ↔ formulaSat env clauses = true := by
  unfold satCount formulaSat
  rw [List.countP_eq_length, List.all_eq_true]
  constructor
  · intro h c hc
    exact h c hc
  · intro h c hc
    exact h c hc

-- --------------------------------------- multiK as explicit commonK rows

/-- The instance `multiK` builds for the row at `env`. -/
def rowInstM (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) (env : Nat) : Instance MVertex where
  verts := (assemble P parts g clauses).1
  edges := (assemble P parts g clauses).2
  anchors := (List.range ((P.attach parts).1.parts.length - parts.length)).map
    MVertex.anchor
  selected := (List.range (varCount clauses)).map fun v =>
    if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v
  forbidden := (List.range (varCount clauses)).map fun v =>
    if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v

theorem multiK_rows_eq (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec)
    (hok : negLayerOk P (P.attach parts).1 = true) :
    multiK P parts g clauses
      = commonK P ((List.range (2 ^ varCount clauses)).map fun env =>
          (formulaSat env clauses, rowInstM P parts g clauses env)) := by
  unfold multiK rowInstM
  rcases h : P.attach parts with ⟨U, forced⟩
  rw [h] at hok
  simp only at hok
  simp [hok]

-- --------------------------------------------------- variable-count bounds

theorem foldl_max_var_le : ∀ (c : ClauseSpec) (acc : Nat),
    acc ≤ c.foldl (fun m l => Nat.max m (l.1 + 1)) acc := by
  intro c
  induction c with
  | nil => intro acc; exact Nat.le_refl _
  | cons l t ih =>
    intro acc
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_var_mem : ∀ (c : ClauseSpec) {l : Nat × Bool}, l ∈ c →
    ∀ acc, l.1 + 1 ≤ c.foldl (fun m l => Nat.max m (l.1 + 1)) acc := by
  intro c
  induction c with
  | nil =>
    intro l hl
    cases hl
  | cons a t ih =>
    intro l hl acc
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_var_le t _)
    · exact ih hl' _

theorem varCount_outer_le : ∀ (cs : List ClauseSpec) (acc : Nat),
    acc ≤ cs.foldl (fun a c => c.foldl (fun m l => Nat.max m (l.1 + 1)) a) acc := by
  intro cs
  induction cs with
  | nil => intro acc; exact Nat.le_refl _
  | cons c t ih =>
    intro acc
    rw [List.foldl_cons]
    exact Nat.le_trans (foldl_max_var_le c acc) (ih _)

theorem varCount_go_bound : ∀ (cs : List ClauseSpec) (acc : Nat)
    {clause : ClauseSpec}, clause ∈ cs → ∀ {l : Nat × Bool}, l ∈ clause →
    l.1 < cs.foldl (fun a c => c.foldl (fun m l => Nat.max m (l.1 + 1)) a) acc := by
  intro cs
  induction cs with
  | nil =>
    intro acc clause hcl
    cases hcl
  | cons c t ih =>
    intro acc clause hcl l hl
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hcl with rfl | hcl'
    · have h1 := foldl_max_var_mem clause hl acc
      have h2 := varCount_outer_le t
        (clause.foldl (fun m l => Nat.max m (l.1 + 1)) acc)
      omega
    · exact ih _ hcl' hl

/-- Every variable of the formula lies below `varCount`. -/
theorem varCount_bound {clauses : List ClauseSpec} {clause : ClauseSpec}
    (hcl : clause ∈ clauses) {l : Nat × Bool} (hl : l ∈ clause) :
    l.1 < varCount clauses :=
  varCount_go_bound clauses 0 hcl hl

theorem envOf_lt (clause : ClauseSpec) (env : Nat) : envOf clause env < 8 := by
  unfold envOf
  cases h0 : litSat env (clause.getD 0 (0, true)) <;>
    cases h1 : litSat env (clause.getD 1 (0, true)) <;>
      cases h2 : litSat env (clause.getD 2 (0, true)) <;> decide

theorem all_range_getD {β : Type} (d : β) (q : β → Bool) (l : List β) :
    (List.range l.length).all (fun c => q (l.getD c d)) = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.all_cons, List.all_map,
      all_congr' (p := (fun c => q ((a :: l).getD c d)) ∘ Nat.succ)
        (q := fun c => q (l.getD c d)) (fun _ _ => rfl),
      ih, List.all_cons]
    rfl

-- ------------------------------- the feasibility kit at the formula level

/-- Kit-level aggregation for feasibility problems: once every row's
    predicate agrees with formula satisfiability (the per-problem
    obligation), the whole 2^n-row table reads budget 1 exactly when
    the formula is satisfiable. Pure `commonK` algebra. -/
theorem feasibility_multiK_iff (name : String)
    (ok : {β : Type} → [BEq β] → Instance β → Bool)
    (attach : List Nat → Universe × List Edge) (layer : Nat → List MEdge)
    (viable : {β : Type} → [BEq β] → Instance β → Bool)
    (parts : List Nat) (g : List Edge) (clauses : List ClauseSpec)
    (hrow : ∀ env, env < 2 ^ varCount clauses →
      ok (rowInstM (feasibility name ok attach layer viable) parts g clauses
        env) = formulaSat env clauses) :
    (multiK (feasibility name ok attach layer viable) parts g clauses
        = some 1
      ↔ ∃ env, env < 2 ^ varCount clauses ∧ formulaSat env clauses = true) := by
  rw [multiK_rows_eq _ _ _ _ rfl, commonK_eq_some_iff]
  constructor
  · rintro ⟨⟨r, hr, hsat⟩, _⟩
    obtain ⟨env, henv, rfl⟩ := List.mem_map.mp hr
    exact ⟨env, List.mem_range.mp henv, hsat⟩
  · rintro ⟨env₀, henv₀, hsat₀⟩
    constructor
    · exact ⟨_, List.mem_map.mpr ⟨env₀, List.mem_range.mpr henv₀, rfl⟩, hsat₀⟩
    · rintro r hr
      obtain ⟨env, henv, rfl⟩ := List.mem_map.mp hr
      have h := hrow env (List.mem_range.mp henv)
      unfold rowCond
      simp only [feasibility] at h ⊢
      cases hf : formulaSat env clauses <;> rw [hf] at h <;> simp [h]

end Atlas
