import search.ProofsCover
import search.Space

/-!
  The search procedure visits every candidate and reports only candidates.

  `searchSlice threeColoring parts true` is the search over one orbit
  composition. It walks all subsets of the free edge orbits, depth first,
  prunes a subtree as soon as a satisfiable row has become uncolorable, and
  lists in `found` the graphs that pass the check on the four input classes.

  * `searchSlice_complete`: every S3-symmetric candidate that passes the
    judge is found. The list `found` contains a graph with the same edge
    set. The walk enumerates every subset of the free orbits
    (`searchAux_complete`), pruning loses nothing because adding edges never
    makes an uncolorable row colorable (`threeColoring_kill`), every
    S3-invariant graph is a union of orbits (`exists_graph_of_invariant`),
    and for an invariant graph the four input classes decide the eight
    inputs (`gadgetK_s3_symmetry_reduction_threeColoring`).
  * `searchSlice_sound`: every found graph is an S3-symmetric candidate
    that passes the judge.

  Both are proved by induction on the walk. No run of the search is used.
-/

namespace Atlas

open List

-- ------------------------------------------------------------ completeness

/-- Completeness of the found list: a graph of the walk that passes
    `gadgetK` puts its leaf graph (a permutation of it) in the found
    list. -/
theorem gadgetK_mem_found_threeColoring (parts : List Nat) (symmetry : Bool)
    (mask k : Nat)
    (hg : gadgetK threeColoring parts
        (graphAt ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).1
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 symmetry).2 mask) symmetry
      = some k) :
    (walkGraph ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 mask
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1, k)
      ∈ (searchSlice threeColoring parts symmetry).2.found := by
  rw [gadgetK_3col_eq] at hg
  have hperm := walkGraph_perm_graphAt
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).1
    ((threeColoring.attach parts).1.splitForced
      (threeColoring.attach parts).2 symmetry).2 mask
  have hchk : checkGadget threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry)
      (walkGraph ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 mask
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1) = some k := by
    rw [checkGadget_perm_3col _ _ _ hperm]
    exact hg
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
  rw [hfound]
  exact List.mem_reverse.mpr hmem

/-- The search is complete: every S3-symmetric candidate of the composition
    `parts` that passes the judge on the eight inputs is found. The list
    `found` of the search contains a graph with the same edge set and the
    same verdict. -/
theorem searchSlice_complete (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) {g : List Edge}
    (hsym : Statement.SymCandidate parts g) {b : Nat}
    (hK : gadgetK threeColoring parts g false = some b) :
    ∃ g', (g', b) ∈ (searchSlice threeColoring parts true).2.found ∧
      ∀ e, e ∈ g ↔ e ∈ g' := by
  obtain ⟨hsub, hinv, hforced⟩ := hsym
  have hU := attach_legal parts hparts
  -- the candidate has the edge set of a graph of the walk
  obtain ⟨g'', hg'', hmem⟩ := exists_graph_of_invariant hU rfl _ hsub hinv hforced
  rw [gadgetK_congr_3col parts false (fun e he => edges_ne (hsub e he)) hmem] at hK
  -- on a graph of the walk the four input classes decide the eight inputs
  obtain ⟨hsub'', hcl''⟩ :=
    graphs_symmetric_props hU rfl (threeColoring.attach parts).2 g'' hg''
  rw [← gadgetK_s3_symmetry_reduction_threeColoring parts hparts hsub'' hcl''] at hK
  unfold Universe.graphs at hg''
  obtain ⟨mask, _, rfl⟩ := List.mem_map.mp hg''
  refine ⟨_, gadgetK_mem_found_threeColoring parts true mask b hK, fun e => ?_⟩
  rw [hmem e]
  exact (walkGraph_perm_graphAt _ _ mask).mem_iff.symm

-- --------------------------------------------------------------- soundness

theorem walkGraph_cons_odd (g : List Edge) (rest : List (List Edge)) (m : Nat)
    (acc : List Edge) :
    walkGraph (g :: rest) (2 * m + 1) acc = walkGraph rest m (g ++ acc) := by
  have hb : (2 * m + 1) &&& 1 = 1 := by
    rw [Nat.and_one_is_mod]
    omega
  simp only [walkGraph, hb, twoMulAdd_shift]
  rfl

theorem walkGraph_cons_even (g : List Edge) (rest : List (List Edge)) (m : Nat)
    (acc : List Edge) :
    walkGraph (g :: rest) (2 * m) acc = walkGraph rest m acc := by
  have hb : (2 * m) &&& 1 = 0 := by
    rw [Nat.and_one_is_mod]
    omega
  simp only [walkGraph, hb, twoMul_shift]
  rfl

/-- Every find of the walk is the leaf graph of a branch, and it passes the
    check. -/
theorem searchAux_sound (P : Problem) (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex)) :
    ∀ (free : List (List Edge)) (acc : List Edge) (stats : SliceStats)
      (x : List Edge × Nat),
      x ∈ (searchAux P U anchors rows free acc stats).found →
      x ∈ stats.found ∨
        ∃ mask, x.1 = walkGraph free mask acc ∧
          checkGadget P U anchors rows x.1 = some x.2 := by
  intro free
  induction free with
  | nil =>
    intro acc stats x hx
    cases hchk : checkGadget P U anchors rows acc with
    | none =>
      simp only [searchAux, hchk] at hx
      exact Or.inl hx
    | some k =>
      simp only [searchAux, hchk] at hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact Or.inr ⟨0, rfl, hchk⟩
      · exact Or.inl h
  | cons g rest ih =>
    intro acc stats x hx
    simp only [searchAux] at hx
    split at hx
    · rcases ih acc _ x hx with h | ⟨m, h1, h2⟩
      · rcases ih (g ++ acc) stats x h with h' | ⟨m, h1, h2⟩
        · exact Or.inl h'
        · exact Or.inr ⟨2 * m + 1, by rw [walkGraph_cons_odd]; exact h1, h2⟩
      · exact Or.inr ⟨2 * m, by rw [walkGraph_cons_even]; exact h1, h2⟩
    · rcases ih acc _ x hx with h | ⟨m, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨2 * m, by rw [walkGraph_cons_even]; exact h1, h2⟩

/-- The base and the free switches of the symmetric walk lie in the edge
    list and are closed under the action. -/
theorem splitForced_props {U : Universe} (hU : U.legal) (hll : U.litLit = false)
    (forced : List Edge) :
    (∀ e ∈ (U.splitForced forced true).1, e ∈ U.edges) ∧
    (∀ s ∈ perms, ∀ e ∈ (U.splitForced forced true).1,
      U.actEdge s e ∈ (U.splitForced forced true).1) ∧
    ∀ o ∈ (U.splitForced forced true).2, (∀ e ∈ o, e ∈ U.edges) ∧
      ∀ s ∈ perms, ∀ e ∈ o, U.actEdge s e ∈ o := by
  have hsw : U.switches true = U.orbits := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨o, ho, heo⟩ := List.mem_flatten.mp he
    have ho' : o ∈ U.orbits := hsw ▸ (List.mem_filter.mp ho).1
    exact (orbit_switch_props hU hll ho').1 e heo
  · intro s hs e he
    obtain ⟨o, ho, heo⟩ := List.mem_flatten.mp he
    have ho' : o ∈ U.orbits := hsw ▸ (List.mem_filter.mp ho).1
    exact List.mem_flatten.mpr
      ⟨o, ho, (orbit_switch_props hU hll ho').2 s hs e heo⟩
  · intro o ho
    have ho' : o ∈ U.orbits := hsw ▸ (List.mem_filter.mp ho).1
    exact orbit_switch_props hU hll ho'

/-- The forced edges are in the base of the symmetric walk. -/
theorem forced_mem_base {U : Universe} (hU : U.legal) (forced : List Edge)
    (hf : ∀ f ∈ forced, normEdge f ∈ U.edges) :
    ∀ f ∈ forced, normEdge f ∈ (U.splitForced forced true).1 := by
  intro f hfm
  obtain ⟨o, ho, hfo⟩ := orbits_cover hU (hf f hfm)
  have hsw : U.switches true = U.orbits := rfl
  refine List.mem_flatten.mpr ⟨o, List.mem_filter.mpr ⟨hsw ▸ ho, ?_⟩, hfo⟩
  exact List.any_eq_true.mpr
    ⟨normEdge f, List.mem_map.mpr ⟨f, hfm, rfl⟩, List.contains_iff_mem.mpr hfo⟩

theorem attach_lit_mem (parts : List Nat) {i : Nat} (hi : i < 3) :
    Vertex.lit i ∈ (threeColoring.attach parts).1.vertices :=
  mem_vertices.mpr (Or.inl ⟨i, hi, rfl⟩)

theorem attach_anchor_mem (parts : List Nat) {d : Nat} (hd : d < 3) :
    Vertex.aux (parts.length + d) 0 ∈ (threeColoring.attach parts).1.vertices := by
  refine mem_vertices.mpr (Or.inr ⟨parts.length + d, 0, ?_, ?_, rfl⟩)
  · rw [attach_parts, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [attach_size parts hd]
    exact Nat.one_pos

/-- The forced edges, the palette triangle and the edges from the literals
    to G_B, are pairs of the candidate space. -/
theorem attach_forced_mem_edges (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) :
    ∀ f ∈ (threeColoring.attach parts).2,
      normEdge f ∈ (threeColoring.attach parts).1.edges := by
  have hU := attach_legal parts hparts
  have hT := attach_anchor_mem parts (d := 0) (by decide)
  have hF := attach_anchor_mem parts (d := 1) (by decide)
  have hB := attach_anchor_mem parts (d := 2) (by decide)
  have hne : ∀ a b : Nat, a ≠ b → (Vertex.aux a 0 : Vertex) ≠ .aux b 0 :=
    fun a b hab h => hab (Vertex.aux.inj h).1
  intro f hf
  have hforced : (threeColoring.attach parts).2 =
      [(Vertex.aux parts.length 0, Vertex.aux (parts.length + 1) 0),
       (Vertex.aux (parts.length + 1) 0, Vertex.aux (parts.length + 2) 0),
       (Vertex.aux (parts.length + 2) 0, Vertex.aux parts.length 0),
       (Vertex.lit 0, Vertex.aux (parts.length + 2) 0),
       (Vertex.lit 1, Vertex.aux (parts.length + 2) 0),
       (Vertex.lit 2, Vertex.aux (parts.length + 2) 0)] := rfl
  rw [hforced] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_edges_of_norm hU hT hF (hne _ _ (by omega))
      (fun i j h => Vertex.noConfusion h.1)
  · exact mem_edges_of_norm hU hF hB (hne _ _ (by omega))
      (fun i j h => Vertex.noConfusion h.1)
  · exact mem_edges_of_norm hU hB hT (hne _ _ (by omega))
      (fun i j h => Vertex.noConfusion h.1)
  · exact mem_edges_of_norm hU (attach_lit_mem parts (by decide)) hB
      (fun h => Vertex.noConfusion h) (fun i j h => Vertex.noConfusion h.2)
  · exact mem_edges_of_norm hU (attach_lit_mem parts (by decide)) hB
      (fun h => Vertex.noConfusion h) (fun i j h => Vertex.noConfusion h.2)
  · exact mem_edges_of_norm hU (attach_lit_mem parts (by decide)) hB
      (fun h => Vertex.noConfusion h) (fun i j h => Vertex.noConfusion h.2)

/-- The search is sound: every found graph is an S3-symmetric candidate of
    the composition, and it passes the judge on the eight inputs with the
    reported verdict. -/
theorem searchSlice_sound (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) :
    ∀ x ∈ (searchSlice threeColoring parts true).2.found,
      Statement.SymCandidate parts x.1 ∧
        gadgetK threeColoring parts x.1 false = some x.2 := by
  intro x hx
  have hU := attach_legal parts hparts
  have hfound : (searchSlice threeColoring parts true).2.found
      = ((searchAux threeColoring (threeColoring.attach parts).1
          (anchorsOf parts.length (threeColoring.attach parts).1)
          (gadgetRows threeColoring true)
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 true).2
          ((threeColoring.attach parts).1.splitForced
            (threeColoring.attach parts).2 true).1
          { total := 2 ^ ((threeColoring.attach parts).1.splitForced
              (threeColoring.attach parts).2 true).2.length }).found).reverse := by
    rfl
  rw [hfound] at hx
  rcases searchAux_sound _ _ _ _ _ _ _ x (List.mem_reverse.mp hx) with h | ⟨mask, h1, h2⟩
  · exact absurd h List.not_mem_nil
  · -- the leaf graph is a permutation of a graph of the walk
    have hperm := walkGraph_perm_graphAt
      ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 true).1
      ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 true).2 mask
    obtain ⟨hbs, hbc, hfr⟩ := splitForced_props hU rfl (threeColoring.attach parts).2
    obtain ⟨hgs, hgc⟩ := graphAt_props hbs hbc hfr mask
    have hsub : ∀ e ∈ x.1, e ∈ (threeColoring.attach parts).1.edges := by
      intro e he
      rw [h1] at he
      exact hgs e (hperm.mem_iff.mp he)
    have hinv : ∀ s ∈ perms, ∀ e ∈ x.1,
        (threeColoring.attach parts).1.actEdge s e ∈ x.1 := by
      intro s hs e he
      rw [h1] at he ⊢
      exact hperm.mem_iff.mpr (hgc s hs e (hperm.mem_iff.mp he))
    refine ⟨⟨hsub, hinv, ?_⟩, ?_⟩
    · intro f hf
      rw [h1]
      exact (walkGraph_sublist _ mask _).subset
        (forced_mem_base hU _ (attach_forced_mem_edges parts hparts) f hf)
    · rw [← gadgetK_s3_symmetry_reduction_threeColoring parts hparts hsub hinv,
        gadgetK_3col_eq]
      exact h2

end Atlas
