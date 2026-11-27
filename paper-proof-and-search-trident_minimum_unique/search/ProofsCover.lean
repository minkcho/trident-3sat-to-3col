import search.Proofs
import search.ProofsSym
/-!
  Coverage of the orbit generator and the converse enumeration theorem.

  `ProofsSym.lean` proves that every enumerated symmetric candidate is an
  S3-invariant subgraph of the universe (`graphs_symmetric_props`). This
  file proves the converse: every S3-invariant graph inside the edge
  list that contains the forced base has the same edge SET as some
  enumerated candidate (`exists_graph_of_invariant`). The ingredients
  are coverage -- every edge lies in some emitted switch
  (`orbits_cover`) -- and orbit transitivity (`mem_orbit_trans`).

  With the membership-level congruence of the 3-coloring check
  (`gadgetK_congr_3col`), statements about the enumerated list hold for
  every invariant graph. `Search.lean` uses this for the completeness of
  the search.
-/

namespace Atlas

open List

-- ------------------------------------------------ the generator covers

/-- The generator's loop: every input edge not already seen ends up in
    some emitted orbit. -/
theorem orbits_go_cover {U : Universe} (hU : U.legal) :
    ∀ (l seen : List Edge), (∀ e ∈ l, e ∈ U.edges) →
      ∀ e ∈ l, e ∉ seen → ∃ o ∈ Universe.orbits.go U l seen, e ∈ o := by
  intro l
  induction l with
  | nil => intro seen _ e he; cases he
  | cons e' rest ih =>
    intro seen hsub e he hseen
    simp only [Universe.orbits.go]
    split
    · rename_i hcont
      have he'seen : e' ∈ seen := List.contains_iff_mem.mp hcont
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd he'seen hseen
      · exact ih seen (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) e he hseen
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨U.edgeOrbit e, List.mem_cons_self ..,
          edgeOrbit_self hU (hsub e (List.mem_cons_self ..))⟩
      · by_cases horb : e ∈ U.edgeOrbit e'
        · exact ⟨U.edgeOrbit e', List.mem_cons_self .., horb⟩
        · have hns : e ∉ seen ++ U.edgeOrbit e' := fun h =>
            (List.mem_append.mp h).elim hseen horb
          obtain ⟨o, ho, heo⟩ := ih (seen ++ U.edgeOrbit e')
            (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) e he hns
          exact ⟨o, List.mem_cons_of_mem _ ho, heo⟩

/-- Coverage: every edge of the universe lies in some emitted switch. -/
theorem orbits_cover {U : Universe} (hU : U.legal) {e : Edge}
    (he : e ∈ U.edges) : ∃ o ∈ U.orbits, e ∈ o :=
  orbits_go_cover hU U.edges [] (fun _ hx => hx) e he (by simp)

/-- Orbit transitivity, membership form: inside one orbit the action
    reaches every edge from every other. -/
theorem mem_orbit_trans {U : Universe} (hU : U.legal) (hll : U.litLit = false)
    {e₀ e e' : Edge} (he₀ : e₀ ∈ U.edges) (he : e ∈ U.edgeOrbit e₀)
    (he' : e' ∈ U.edgeOrbit e₀) : ∃ s ∈ perms, U.actEdge s e = e' := by
  have heE : e ∈ U.edges := edgeOrbit_subset_edges hU hll he₀ e he
  obtain ⟨h1, h2, _⟩ := mem_edges heE
  have hsym : e₀ ∈ U.edgeOrbit e := edgeOrbit_symm hU he₀ he
  have hsub : U.edgeOrbit e₀ ⊆ U.edgeOrbit e := edgeOrbit_subset hU h1 h2 hsym
  exact mem_edgeOrbit_iff.mp (hsub he')

-- --------------------------------------- the converse enumeration theorem

/-- Membership in an enumerated candidate: the forced base or a selected
    free switch. -/
theorem mem_graphAt_iff (base : List Edge) (free : List (List Edge))
    (mask : Nat) (e : Edge) :
    e ∈ graphAt base free mask ↔
      e ∈ base ∨ ∃ o ∈ bitSubset mask free, e ∈ o := by
  unfold graphAt
  rw [graphAt_selector free mask, List.mem_append, List.mem_flatten]

/-- Every S3-invariant graph inside the edge list that contains the
    (normalized) forced edges has the edge set of some enumerated
    symmetric candidate. -/
theorem exists_graph_of_invariant {U : Universe} (hU : U.legal)
    (hll : U.litLit = false) (forced : List Edge) {g : List Edge}
    (hsub : ∀ e ∈ g, e ∈ U.edges)
    (hinv : ∀ s ∈ perms, ∀ e ∈ g, U.actEdge s e ∈ g)
    (hforced : ∀ f ∈ forced, normEdge f ∈ g) :
    ∃ g' ∈ U.graphs (symmetry := true) (forced := forced),
      ∀ e, e ∈ g ↔ e ∈ g' := by
  -- an orbit that meets g lies inside g
  have horb : ∀ o ∈ U.orbits, ∀ e ∈ o, e ∈ g → ∀ e' ∈ o, e' ∈ g := by
    intro o ho e he heg e' he'
    obtain ⟨e₀, he₀, rfl⟩ := orbits_spec U o ho
    obtain ⟨s, hs, rfl⟩ := mem_orbit_trans hU hll he₀ he he'
    exact hinv s hs e heg
  have hsw : U.switches true = U.orbits := rfl
  unfold Universe.graphs Universe.splitForced
  simp only [hsw]
  -- the selected free switches: those inside g
  obtain ⟨mask, hlt, hbs⟩ := exists_bitSubset
    (List.filter_sublist (p := fun o : List Edge => o.all fun e => g.contains e)
      (l := U.orbits.filter fun o => !(forced.map normEdge).any o.contains))
  refine ⟨_, List.mem_map.mpr ⟨mask, List.mem_range.mpr hlt, rfl⟩, ?_⟩
  intro e
  rw [mem_graphAt_iff, hbs]
  constructor
  · intro heg
    obtain ⟨o, ho, heo⟩ := orbits_cover hU (hsub e heg)
    have hog : ∀ e' ∈ o, e' ∈ g := horb o ho e heo heg
    by_cases hf : (forced.map normEdge).any o.contains = true
    · exact Or.inl (List.mem_flatten.mpr ⟨o, List.mem_filter.mpr ⟨ho, hf⟩, heo⟩)
    · refine Or.inr ⟨o, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨ho, ?_⟩, ?_⟩, heo⟩
      · simpa using hf
      · exact List.all_eq_true.mpr fun e' he' =>
          List.contains_iff_mem.mpr (hog e' he')
  · rintro (hb | ⟨o, ho, heo⟩)
    · obtain ⟨o, ho, heo⟩ := List.mem_flatten.mp hb
      have ho' := List.mem_filter.mp ho
      obtain ⟨f, hf, hfo⟩ := List.any_eq_true.mp ho'.2
      obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      exact horb o ho'.1 _ (List.contains_iff_mem.mp hfo) (hforced f₀ hf₀) e heo
    · have ho' := List.mem_filter.mp ho
      exact List.contains_iff_mem.mp (List.all_eq_true.mp ho'.2 e heo)

-- ------------------------------ the 3-coloring check sees the edge set

/-- `checkGadget` for 3-coloring depends on a loop-free graph only through
    its edge set. -/
theorem checkGadget_congr_3col (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex)) {g g' : List Edge}
    (hloop : ∀ e ∈ g, e.1 ≠ e.2) (h : ∀ e, e ∈ g ↔ e ∈ g') :
    checkGadget threeColoring U anchors rows g
      = checkGadget threeColoring U anchors rows g' := by
  unfold checkGadget
  apply commonK_ext
  refine forall₂_map_map ?_
  intro r _
  obtain ⟨isSat, sel, forb⟩ := r
  dsimp only
  have hloop' : ∀ a : Vertex, a ∉ adjTo g a := by
    intro a ha
    rcases mem_adjTo.mp ha with h' | h' <;> exact hloop _ h' rfl
  have hco : colorsOk { verts := U.vertices, edges := g, anchors := anchors, selected := sel, forbidden := forb } = colorsOk { verts := U.vertices, edges := g', anchors := anchors, selected := sel, forbidden := forb } := by
    unfold colorsOk
    exact colorable_congr_edges U.vertices _ hloop' (vertices_nodup U)
      (adjTo_congr_mem h)
  refine ⟨rfl, ?_, ?_⟩
  · simp only [threeColoring, feasibility, hco]
  · intro k
    simp only [threeColoring, feasibility, hco]

theorem gadgetK_congr_3col (parts : List Nat) (symmetry : Bool)
    {g g' : List Edge} (hloop : ∀ e ∈ g, e.1 ≠ e.2)
    (h : ∀ e, e ∈ g ↔ e ∈ g') :
    gadgetK threeColoring parts g symmetry
      = gadgetK threeColoring parts g' symmetry := by
  rw [gadgetK_3col_eq, gadgetK_3col_eq]
  exact checkGadget_congr_3col _ _ _ hloop h

end Atlas
