import search.ProofsColorK
/-!
  Pruning soundness. The 3-coloring `viable` bound is antitone in the edge
  set (`colorsOk_antitone`): the walk asks `viable` of a partial graph, and
  every extension only adds edges, so once a satisfiable row is dead it stays
  dead and no valid gadget lives in the pruned subtree. The kernel-level fact
  is the k = 3 instance of `colorableGoK_antitone` (ProofsColorK).
  `ProofsWalk` consumes it through `threeColoring_kill`.
-/

namespace Atlas

open List

/-- The backtracking kernel is antitone in the edge set: a proper coloring
    under more edges is proper under fewer -- the k = 3 instance of
    `colorableGoK_antitone`, through the bridge. -/
theorem colorableGo_antitone {α : Type} [BEq α] {edges edges' : List (α × α)}
    (h : edges <+ edges') (pins : List (α × Nat)) :
    ∀ (rest : List α) (assign : List (α × Nat)),
      colorableGo edges' pins rest assign = true →
      colorableGo edges pins rest assign = true := by
  intro rest assign
  rw [colorableGo_eq_colorableGoK3, colorableGo_eq_colorableGoK3]
  exact colorableGoK_antitone h pins rest assign

theorem colorable_antitone {α : Type} [BEq α] {edges edges' : List (α × α)}
    (h : edges <+ edges') (verts : List α) (pins : List (α × Nat)) :
    colorable edges' verts pins = true → colorable edges verts pins = true :=
  colorableGo_antitone h pins verts []

/-- The 3-coloring viable bound is antitone in the edge set: once a partial
    graph fails it, every extension fails it too, so pruning a subtree
    whose satisfiable row already died loses no valid gadget. -/
theorem colorsOk_antitone {α : Type} [BEq α] {i i' : Instance α}
    (hv : i.verts = i'.verts) (ha : i.anchors = i'.anchors)
    (hs : i.selected = i'.selected) (hf : i.forbidden = i'.forbidden)
    (he : i.edges <+ i'.edges) : colorsOk i' = true → colorsOk i = true := by
  intro h
  unfold colorsOk at h ⊢
  rw [hv, ha, hs, hf]
  exact colorable_antitone he _ _ h

end Atlas
