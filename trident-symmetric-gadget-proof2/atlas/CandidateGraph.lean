import atlas.Candidate

/-!
  The graph of a gadget as a symmetric candidate.

  `g.edgeList` lists the edges of the gadget in the engine's vertices
  (`g.toVertex`). Adjacency in the gadget is membership in this list
  (`adj_iff`), and the list is an S3-symmetric candidate of the composition
  `g.parts` (`symCandidate`): it lies in the candidate space, it is closed
  under the engine's action, and it contains the forced edges.
-/

namespace Def1

open Atlas MulAction

/-- A normalized edge is the pair or the reversed pair. -/
theorem normEdge_cases (a b : Vertex) :
    normEdge (a, b) = (a, b) ∨ normEdge (a, b) = (b, a) := by
  unfold normEdge
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The engine's action on a normalized edge. -/
theorem actEdge_normEdge {U : Universe} (hU : U.legal) {s : Atlas.Perm}
    (hs : s ∈ perms) {a b : Vertex} (ha : a ∈ U.vertices) (hb : b ∈ U.vertices) :
    U.actEdge s (normEdge (a, b)) = normEdge (U.act s a, U.act s b) := by
  rcases normEdge_cases a b with h | h
  · rw [h]
    rfl
  · rw [h]
    show normEdge (U.act s b, U.act s a) = normEdge (U.act s a, U.act s b)
    exact normEdge_comm hU (act_mem hU hs hb) (act_mem hU hs ha)

variable {V : Type}

namespace Gadget

variable (g : Gadget V) [Finite V]

open Classical in
/-- The edges of the gadget, written in the engine's vertices and
    normalized. -/
noncomputable def edgeList : List Edge :=
  g.U.edges.filter fun e =>
    decide (∃ u v, g.G.Adj u v ∧ e = normEdge (g.toVertex u, g.toVertex v))

/-- An edge of the gadget is a pair of the candidate space: its ends are
    different vertices of the universe, and they are not both literals. -/
theorem normEdge_mem_edges {u v : V} (h : g.G.Adj u v) :
    normEdge (g.toVertex u, g.toVertex v) ∈ g.U.edges := by
  refine mem_edges_of_norm g.U_legal (g.toVertex_mem u) (g.toVertex_mem v)
    (fun he => h.ne (g.toVertex_injective he)) ?_
  rintro i j ⟨hi, hj⟩
  obtain ⟨i', rfl⟩ := g.eq_lit_of_toVertex hi
  obtain ⟨j', rfl⟩ := g.eq_lit_of_toVertex hj
  exact g.lit_nonadj i' j' h

open Classical in
theorem mem_edgeList {e : Edge} :
    e ∈ g.edgeList ↔
      ∃ u v, g.G.Adj u v ∧ e = normEdge (g.toVertex u, g.toVertex v) := by
  unfold edgeList
  rw [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · rintro ⟨u, v, huv, rfl⟩
    exact ⟨g.normEdge_mem_edges huv, u, v, huv, rfl⟩

/-- Adjacency in the gadget is membership in the edge list. -/
theorem adj_iff {u v : V} :
    g.G.Adj u v ↔ normEdge (g.toVertex u, g.toVertex v) ∈ g.edgeList := by
  constructor
  · exact fun h => g.mem_edgeList.mpr ⟨u, v, h, rfl⟩
  · intro h
    obtain ⟨u', v', h', he⟩ := g.mem_edgeList.mp h
    rcases normEdge_cases (g.toVertex u) (g.toVertex v) with h1 | h1 <;>
      rcases normEdge_cases (g.toVertex u') (g.toVertex v') with h2 | h2 <;>
      rw [h1, h2] at he <;>
      obtain ⟨e1, e2⟩ := Prod.mk.inj he
    · rw [g.toVertex_injective e1, g.toVertex_injective e2]
      exact h'
    · rw [g.toVertex_injective e1, g.toVertex_injective e2]
      exact h'.symm
    · rw [g.toVertex_injective e1, g.toVertex_injective e2]
      exact h'.symm
    · rw [g.toVertex_injective e1, g.toVertex_injective e2]
      exact h'

/-- The neighbors of a vertex in the edge list are the images of its
    neighbors in the gadget. -/
theorem toVertex_mem_adjTo {u v : V} (h : g.G.Adj u v) :
    g.toVertex v ∈ adjTo g.edgeList (g.toVertex u) := by
  have hm := g.adj_iff.mp h
  rcases normEdge_cases (g.toVertex u) (g.toVertex v) with h1 | h1
  · rw [h1] at hm
    exact mem_adjTo.mpr (Or.inl hm)
  · rw [h1] at hm
    exact mem_adjTo.mpr (Or.inr hm)

theorem adjTo_edgeList {w w' : Vertex} (h : w' ∈ adjTo g.edgeList w) :
    ∃ u v, g.G.Adj u v ∧ w = g.toVertex u ∧ w' = g.toVertex v := by
  rcases mem_adjTo.mp h with h | h
  · obtain ⟨u, v, huv, he⟩ := g.mem_edgeList.mp h
    rcases normEdge_cases (g.toVertex u) (g.toVertex v) with h1 | h1 <;>
      rw [h1] at he <;> obtain ⟨e1, e2⟩ := Prod.mk.inj he
    · exact ⟨u, v, huv, e1, e2⟩
    · exact ⟨v, u, huv.symm, e1, e2⟩
  · obtain ⟨u, v, huv, he⟩ := g.mem_edgeList.mp h
    rcases normEdge_cases (g.toVertex u) (g.toVertex v) with h1 | h1 <;>
      rw [h1] at he <;> obtain ⟨e1, e2⟩ := Prod.mk.inj he
    · exact ⟨v, u, huv.symm, e2, e1⟩
    · exact ⟨u, v, huv, e2, e1⟩

/-- The forced edges of the candidate space are the palette triangle and
    the edges from `gB` to the literals. -/
theorem forced_eq :
    (threeColoring.attach g.parts).2 =
      [(g.toVertex g.gT, g.toVertex g.gF), (g.toVertex g.gF, g.toVertex g.gB),
       (g.toVertex g.gB, g.toVertex g.gT), (g.toVertex (g.lit 0), g.toVertex g.gB),
       (g.toVertex (g.lit 1), g.toVertex g.gB), (g.toVertex (g.lit 2), g.toVertex g.gB)] := by
  rw [toVertex_gT, toVertex_gF, toVertex_gB, toVertex_lit, toVertex_lit, toVertex_lit]
  show [(Vertex.aux g.parts.length 0, Vertex.aux (g.parts.length + 1) 0),
      (Vertex.aux (g.parts.length + 1) 0, Vertex.aux (g.parts.length + 2) 0),
      (Vertex.aux (g.parts.length + 2) 0, Vertex.aux g.parts.length 0),
      (Vertex.lit 0, Vertex.aux (g.parts.length + 2) 0),
      (Vertex.lit 1, Vertex.aux (g.parts.length + 2) 0),
      (Vertex.lit 2, Vertex.aux (g.parts.length + 2) 0)] = _
  rw [parts_length]
  rfl

/-- The graph of the gadget is an S3-symmetric candidate of the orbit
    composition `g.parts`. -/
theorem symCandidate : Statement.SymCandidate g.parts g.edgeList := by
  refine ⟨fun e he => (List.mem_filter.mp he).1, ?_, ?_⟩
  · intro s hs e he
    obtain ⟨σ, rfl⟩ := toTable_surj s hs
    obtain ⟨u, v, huv, rfl⟩ := g.mem_edgeList.mp he
    refine g.mem_edgeList.mpr ⟨g.ρ σ u, g.ρ σ v, (g.ρ σ).map_rel_iff.mpr huv, ?_⟩
    rw [g.toVertex_map, g.toVertex_map]
    exact actEdge_normEdge g.U_legal hs (g.toVertex_mem u) (g.toVertex_mem v)
  · intro f hf
    rw [g.forced_eq] at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact g.mem_edgeList.mpr ⟨_, _, g.palette.1, rfl⟩
    · exact g.mem_edgeList.mpr ⟨_, _, g.palette.2.1, rfl⟩
    · exact g.mem_edgeList.mpr ⟨_, _, g.palette.2.2, rfl⟩
    · exact g.mem_edgeList.mpr ⟨_, _, (g.fan 0).symm, rfl⟩
    · exact g.mem_edgeList.mpr ⟨_, _, (g.fan 1).symm, rfl⟩
    · exact g.mem_edgeList.mpr ⟨_, _, (g.fan 2).symm, rfl⟩

end Gadget

end Def1
