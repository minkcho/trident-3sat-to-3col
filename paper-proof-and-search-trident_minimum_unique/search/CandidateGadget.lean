import proof.Basics
import search.CandidateValid

/-!
  From a candidate of the search engine to a gadget of Definition 1.

  `Candidate.lean`, `CandidateGraph.lean` and `CandidateValid.lean` turn a
  gadget of Definition 1 into a candidate of the search. This file goes the
  other way. Let `C` be an S3-symmetric candidate: an orbit composition
  with part sizes in {1, 2, 3, 6} and an edge list in the candidate space
  that is closed under the engine's action and contains the forced edges.
  Its vertices, with the edge list as adjacency and the engine's action, are
  an S3-symmetric clause gadget in the sense of Definition 1
  (`Candidate.gadget`). The gadget has `C.parts.sum` auxiliary vertices
  (`card_aux`), and it is valid exactly when the candidate passes the
  engine's judge (`valid_iff`).

  So the candidate space of the search is the set of gadgets of
  Definition 1, in both directions.
-/

namespace Def1

open Atlas

-- ------------------------------------------------------- counting vertices

theorem sum_map_getD (l : List Nat) :
    ((List.range l.length).map fun p => l.getD p 0).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.sum_cons]
    have h : ((fun p => (a :: t).getD p 0) ∘ Nat.succ) = fun p => t.getD p 0 := by
      funext p
      simp
    rw [h, ih]
    rfl

/-- A universe has three literals and one vertex for each unit of its
    parts. -/
theorem vertices_length (U : Universe) : U.vertices.length = U.parts.sum + 3 := by
  unfold Universe.vertices
  rw [List.length_append, List.length_map, List.length_range, List.length_flatMap]
  have h : ((List.range U.parts.length).map fun p =>
      ((List.range (U.size p)).map (Vertex.aux p)).length)
      = (List.range U.parts.length).map fun p => U.parts.getD p 0 := by
    refine List.map_congr_left fun p _ => ?_
    rw [List.length_map, List.length_range]
    rfl
  rw [h, sum_map_getD]
  omega

-- ------------------------------------------------------------ the candidate

/-- An S3-symmetric candidate of the search: an orbit composition with part
    sizes in {1, 2, 3, 6} and an edge list that lies in the candidate space,
    is closed under the engine's action and contains the forced edges. -/
structure Candidate where
  parts : List Nat
  edges : List Edge
  legal : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6
  sym : Statement.SymCandidate parts edges

namespace Candidate

variable (C : Candidate)

/-- The universe of the candidate: its parts and the three anchor parts. -/
abbrev U : Universe := (threeColoring.attach C.parts).1

theorem U_legal : C.U.legal := attach_legal C.parts C.legal

/-- The vertices of the candidate. -/
abbrev Vert : Type := {v : Vertex // v ∈ C.U.vertices}

instance : Finite C.Vert := (List.finite_toSet C.U.vertices).to_subtype

theorem lit_mem (i : Fin 3) : Vertex.lit i.val ∈ C.U.vertices :=
  mem_vertices.mpr (Or.inl ⟨i.val, i.isLt, rfl⟩)

theorem anchor_mem (d : Fin 3) : Vertex.aux (C.parts.length + d.val) 0 ∈ C.U.vertices := by
  refine mem_vertices.mpr (Or.inr ⟨C.parts.length + d.val, 0, ?_, ?_, rfl⟩)
  · show C.parts.length + d.val < (C.parts ++ [1, 1, 1]).length
    rw [List.length_append]
    have := d.isLt
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [attach_size C.parts d.isLt]
    exact Nat.one_pos

/-- An auxiliary part is not an anchor part. -/
theorem aux_mem {p j : Nat} (h : Vertex.aux p j ∈ C.U.vertices) :
    p < C.parts.length + 3 ∧ j < C.U.size p := by
  rcases mem_vertices.mp h with ⟨i, _, hi⟩ | ⟨p', j', hp', hj', he⟩
  · exact Vertex.noConfusion hi
  · obtain ⟨rfl, rfl⟩ := Vertex.aux.inj he
    refine ⟨?_, hj'⟩
    have h1 : C.U.parts.length = C.parts.length + 3 := by
      show (C.parts ++ [1, 1, 1]).length = _
      rw [List.length_append]
      rfl
    omega

/-- The literal `i`. -/
def lit (i : Fin 3) : C.Vert := ⟨.lit i.val, C.lit_mem i⟩

/-- The anchors G_T, G_F, G_B, for `d = 0, 1, 2`. -/
def anchorV (d : Fin 3) : C.Vert := ⟨.aux (C.parts.length + d.val) 0, C.anchor_mem d⟩

-- ------------------------------------------------------------------- action

theorem toTable_one : toTable 1 = (0, 1, 2) := rfl

/-- The engine's action of a permutation on the vertices. -/
def map (σ : Equiv.Perm (Fin 3)) (v : C.Vert) : C.Vert :=
  ⟨C.U.act (toTable σ) v.1, act_mem C.U_legal (toTable_mem σ) v.2⟩

theorem map_id (v : C.Vert) : C.map 1 v = v :=
  Subtype.ext (by
    show C.U.act (toTable 1) v.1 = v.1
    rw [toTable_one]
    exact act_id C.U_legal v.2)

theorem map_comp (σ τ : Equiv.Perm (Fin 3)) (v : C.Vert) :
    C.map (σ * τ) v = C.map σ (C.map τ v) :=
  Subtype.ext (by
    show C.U.act (toTable (σ * τ)) v.1 = C.U.act (toTable σ) (C.U.act (toTable τ) v.1)
    rw [toTable_mul, act_compose C.U (toTable_mem σ) (toTable_mem τ)])

/-- The action is by bijections of the vertex set. -/
def equiv (σ : Equiv.Perm (Fin 3)) : C.Vert ≃ C.Vert where
  toFun := C.map σ
  invFun := C.map σ⁻¹
  left_inv v := by rw [← C.map_comp, inv_mul_cancel, C.map_id]
  right_inv v := by rw [← C.map_comp, mul_inv_cancel, C.map_id]

-- -------------------------------------------------------------------- graph

/-- The graph of the candidate: two vertices are adjacent when their
    normalized pair is in the edge list. -/
def graph : SimpleGraph C.Vert :=
  SimpleGraph.fromRel fun a b => normEdge (a.1, b.1) ∈ C.edges

theorem adj_iff {a b : C.Vert} : C.graph.Adj a b ↔ normEdge (a.1, b.1) ∈ C.edges := by
  unfold graph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rwa [normEdge_comm C.U_legal a.2 b.2]
  · intro h
    refine ⟨fun hab => ?_, Or.inl h⟩
    have he := edges_ne (C.sym.1 _ h)
    rcases normEdge_cases a.1 b.1 with h1 | h1
    · rw [h1] at he
      exact he (congrArg Subtype.val hab)
    · rw [h1] at he
      exact he (congrArg Subtype.val hab).symm

/-- The edge list is closed under the action. -/
theorem mem_map {a b : C.Vert} (σ : Equiv.Perm (Fin 3))
    (h : normEdge (a.1, b.1) ∈ C.edges) :
    normEdge ((C.map σ a).1, (C.map σ b).1) ∈ C.edges := by
  have h1 := C.sym.2.1 (toTable σ) (toTable_mem σ) _ h
  rwa [actEdge_normEdge C.U_legal (toTable_mem σ) a.2 b.2] at h1

/-- The action is by automorphisms of the graph. -/
def iso (σ : Equiv.Perm (Fin 3)) : C.graph ≃g C.graph where
  toEquiv := C.equiv σ
  map_rel_iff' := by
    intro a b
    show C.graph.Adj (C.map σ a) (C.map σ b) ↔ C.graph.Adj a b
    rw [C.adj_iff, C.adj_iff]
    constructor
    · intro h
      have h1 := C.mem_map σ⁻¹ h
      rwa [← C.map_comp, ← C.map_comp, inv_mul_cancel, C.map_id, C.map_id] at h1
    · exact C.mem_map σ

-- ------------------------------------------------------------ forced edges

theorem forced_eq :
    (threeColoring.attach C.parts).2 =
      [(Vertex.aux C.parts.length 0, Vertex.aux (C.parts.length + 1) 0),
       (Vertex.aux (C.parts.length + 1) 0, Vertex.aux (C.parts.length + 2) 0),
       (Vertex.aux (C.parts.length + 2) 0, Vertex.aux C.parts.length 0),
       (Vertex.lit 0, Vertex.aux (C.parts.length + 2) 0),
       (Vertex.lit 1, Vertex.aux (C.parts.length + 2) 0),
       (Vertex.lit 2, Vertex.aux (C.parts.length + 2) 0)] := rfl

/-- The palette triangle is in the edge list. -/
theorem palette_mem :
    normEdge (Vertex.aux C.parts.length 0, Vertex.aux (C.parts.length + 1) 0) ∈ C.edges ∧
    normEdge (Vertex.aux (C.parts.length + 1) 0, Vertex.aux (C.parts.length + 2) 0)
      ∈ C.edges ∧
    normEdge (Vertex.aux (C.parts.length + 2) 0, Vertex.aux C.parts.length 0) ∈ C.edges := by
  refine ⟨C.sym.2.2 _ ?_, C.sym.2.2 _ ?_, C.sym.2.2 _ ?_⟩ <;>
    · rw [C.forced_eq]
      simp

/-- The edges from the literals to G_B are in the edge list. -/
theorem fan_mem (i : Fin 3) :
    normEdge (Vertex.lit i.val, Vertex.aux (C.parts.length + 2) 0) ∈ C.edges := by
  refine C.sym.2.2 _ ?_
  rw [C.forced_eq]
  fin_cases i <;> simp

-- ------------------------------------------------------------------ gadget

/-- The candidate as an S3-symmetric clause gadget of Definition 1. -/
def gadget : Gadget C.Vert where
  G := C.graph
  lit := C.lit
  gT := C.anchorV 0
  gF := C.anchorV 1
  gB := C.anchorV 2
  lit_inj := fun i j h => Fin.ext (Vertex.lit.inj (congrArg Subtype.val h))
  lit_ne_anchor := fun i =>
    ⟨fun h => Vertex.noConfusion (congrArg Subtype.val h),
     fun h => Vertex.noConfusion (congrArg Subtype.val h),
     fun h => Vertex.noConfusion (congrArg Subtype.val h)⟩
  lit_nonadj := fun i j h => by
    have hm := C.sym.1 _ (C.adj_iff.mp h)
    rcases normEdge_cases (Vertex.lit i.val) (Vertex.lit j.val) with h1 | h1
    · exact lit_pair_not_mem (U := C.U) rfl hm (i := i.val) (j := j.val)
        (by show (normEdge (Vertex.lit i.val, Vertex.lit j.val)).1 = _; rw [h1])
        (by show (normEdge (Vertex.lit i.val, Vertex.lit j.val)).2 = _; rw [h1])
    · exact lit_pair_not_mem (U := C.U) rfl hm (i := j.val) (j := i.val)
        (by show (normEdge (Vertex.lit i.val, Vertex.lit j.val)).1 = _; rw [h1])
        (by show (normEdge (Vertex.lit i.val, Vertex.lit j.val)).2 = _; rw [h1])
  palette := ⟨C.adj_iff.mpr C.palette_mem.1, C.adj_iff.mpr C.palette_mem.2.1,
    C.adj_iff.mpr C.palette_mem.2.2⟩
  fan := fun i => (C.adj_iff.mpr (C.fan_mem i)).symm
  ρ :=
    { toFun := C.iso
      map_one' := RelIso.ext fun v => C.map_id v
      map_mul' := fun σ τ => RelIso.ext fun v => C.map_comp σ τ v }
  ρ_lit := fun σ i => Subtype.ext (by
    show Vertex.lit (app (toTable σ) i.val) = Vertex.lit (σ i).val
    rw [app_toTable])
  ρ_anchor := fun σ =>
    ⟨Subtype.ext (act_aux_one _ 0 (attach_size C.parts (d := 0) (by decide))),
     Subtype.ext (act_aux_one _ 0 (attach_size C.parts (d := 1) (by decide))),
     Subtype.ext (act_aux_one _ 0 (attach_size C.parts (d := 2) (by decide)))⟩

-- ---------------------------------------------------------------- counting

theorem card_vert : Nat.card C.Vert = C.parts.sum + 6 := by
  classical
  have : Fintype C.Vert := Fintype.ofFinite _
  have hsum : C.U.parts.sum = C.parts.sum + 3 := by
    show (C.parts ++ [1, 1, 1]).sum = _
    rw [List.sum_append]
    rfl
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype C.U.vertices.toFinset (fun x => List.mem_toFinset),
    List.toFinset_card_of_nodup (vertices_nodup C.U), vertices_length, hsum]

/-- The gadget of a candidate has one auxiliary vertex for each unit of the
    orbit composition. -/
theorem card_aux : Nat.card {v // C.gadget.IsAux v} = C.parts.sum := by
  have h := C.gadget.card_eq
  rw [C.card_vert] at h
  omega

-- ---------------------------------------------------------------- validity

/-- Definition 1 and the engine agree on a row: a proper 3-coloring of the
    gadget extending the input `env` exists exactly when a coloring of the
    candidate respects the pins of the row and gives adjacent vertices
    different colors. -/
theorem specExt_iff_extends (env : Nat) :
    (∃ f, SpecExt C.edges (rowPins C.parts env) C.U.vertices [] f) ↔
      C.gadget.Extends (envInput env) := by
  constructor
  · rintro ⟨f, hpin, hconf⟩
    -- every color is 0, 1 or 2
    have hval : ∀ w ∈ C.U.vertices, f w < 3 := by
      intro w hw
      have hp := hpin w hw
      cases hc : colorAt (rowPins C.parts env) w with
      | none =>
        unfold pinOk at hp
        rw [hc] at hp
        exact hp
      | some cp =>
        rw [pinOk_eq hp hc]
        rcases colorAt_rowPins_iff.mp hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨i, _, rfl⟩
        · omega
        · omega
        · omega
        · split <;> omega
    refine ⟨fun v => ⟨f v.1, hval _ v.2⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro u v huv heq
      have hm := C.adj_iff.mp huv
      have hadj : v.1 ∈ adjTo C.edges u.1 := by
        rcases normEdge_cases u.1 v.1 with h1 | h1
        · rw [h1] at hm
          exact mem_adjTo.mpr (Or.inl hm)
        · rw [h1] at hm
          exact mem_adjTo.mpr (Or.inr hm)
      have hne := hconf u.1 u.2 v.1 hadj
      unfold combined at hne
      rw [if_pos v.2] at hne
      exact hne (congrArg some (congrArg Fin.val heq).symm)
    · exact Fin.ext (pinOk_eq (hpin _ (C.anchorV 0).2)
        (colorAt_rowPins_iff.mpr (Or.inl ⟨rfl, rfl⟩)))
    · exact Fin.ext (pinOk_eq (hpin _ (C.anchorV 1).2)
        (colorAt_rowPins_iff.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · exact Fin.ext (pinOk_eq (hpin _ (C.anchorV 2).2)
        (colorAt_rowPins_iff.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · intro i
      have h : f (Vertex.lit i.val) = if envInput env i = true then 0 else 1 :=
        pinOk_eq (hpin _ (C.lit i).2)
          (colorAt_rowPins_iff.mpr (Or.inr (Or.inr (Or.inr ⟨i, rfl, rfl⟩))))
      apply Fin.ext
      show f (Vertex.lit i.val) = (if envInput env i = true then (0 : Fin 3) else 1).val
      rw [h]
      split <;> rfl
  · rintro ⟨c, hproper, hT, hF, hB, hlit⟩
    classical
    let f : Vertex → Nat := fun w => if h : w ∈ C.U.vertices then (c ⟨w, h⟩).val else 0
    have hf : ∀ (w : Vertex) (hw : w ∈ C.U.vertices), f w = (c ⟨w, hw⟩).val := by
      intro w hw
      show (if h : w ∈ C.U.vertices then (c ⟨w, h⟩).val else 0) = (c ⟨w, hw⟩).val
      rw [dif_pos hw]
    have hflt : ∀ w, f w < 3 := by
      intro w
      show (if h : w ∈ C.U.vertices then (c ⟨w, h⟩).val else 0) < 3
      split
      · exact (c _).isLt
      · omega
    refine ⟨f, ?_, ?_⟩
    · intro w hw
      unfold pinOk
      cases hc : colorAt (rowPins C.parts env) w with
      | none => exact hflt w
      | some cp =>
        show f w = cp
        rcases colorAt_rowPins_iff.mp hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
        · rw [hf _ hw]
          exact congrArg Fin.val hT
        · rw [hf _ hw]
          exact congrArg Fin.val hF
        · rw [hf _ hw]
          exact congrArg Fin.val hB
        · rw [hf _ hw]
          show (c (C.gadget.lit i)).val = _
          rw [hlit i]
          split <;> rfl
    · intro w hw w' hw'
      obtain ⟨hw'm, hne⟩ : ∃ hw'm : w' ∈ C.U.vertices, c ⟨w, hw⟩ ≠ c ⟨w', hw'm⟩ := by
        rcases mem_adjTo.mp hw' with h | h
        · obtain ⟨-, h2, hn⟩ := mem_edges (C.sym.1 _ h)
          refine ⟨h2, hproper _ _ (C.adj_iff.mpr ?_)⟩
          show normEdge (w, w') ∈ C.edges
          rw [hn]
          exact h
        · obtain ⟨h1, -, hn⟩ := mem_edges (C.sym.1 _ h)
          refine ⟨h1, fun heq => hproper _ _ (C.adj_iff.mpr ?_) heq.symm⟩
          show normEdge (w', w) ∈ C.edges
          rw [hn]
          exact h
      unfold combined
      rw [if_pos hw'm, hf _ hw'm, hf _ hw]
      intro h
      exact hne (Fin.ext (Option.some.inj h).symm)

/-- The gadget of a candidate is valid exactly when the candidate passes
    the engine's judge on all eight inputs. -/
theorem valid_iff :
    C.gadget.Valid ↔ gadgetK threeColoring C.parts C.edges false = some 1 := by
  obtain ⟨hjudge, hrow⟩ := Statement.gadgetK_is_validity C.parts C.edges 1
  rw [hjudge]
  constructor
  · intro hv
    refine ⟨rfl, fun env henv => ?_⟩
    rw [hrow C.sym.1 env, C.specExt_iff_extends env, hv (envInput env)]
    exact envInput_some_true env henv
  · rintro ⟨-, h⟩ α
    obtain ⟨env, henv, rfl⟩ := exists_env α
    rw [← C.specExt_iff_extends env, ← hrow C.sym.1 env, h env henv]
    exact (envInput_some_true env henv).symm

end Candidate

end Def1
