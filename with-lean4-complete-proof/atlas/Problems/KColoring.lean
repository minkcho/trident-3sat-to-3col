import atlas.Problems.ThreeColoring
/-!
  The palette-generic backtracking kernel `colorableGoK`: the 3-coloring
  `colorableGo` with the unpinned choice list [0, 1, 2] abstracted to
  `List.range k`. One kernel, one antitonicity lemma and one spec
  reflection (atlas/ProofsColorK.lean) serve every palette size, and the
  3-coloring kernel is its k = 3 instance (`colorableGo_eq_colorableGoK3`).
  In the full line this lives in Problems/Bipartization.lean, whose
  bipartiteness test is the k = 2 instance.
-/

namespace Atlas

/-- Palette-generic backtracking kernel: `colorableGo` with `k` colors.
    Total (structural on the remaining vertices) so that
    `atlas/ProofsColorK.lean` can prove it antitone in the edge set and
    reflect it into an existence spec. -/
def colorableGoK {α : Type} [BEq α] (k : Nat) (edges : List (α × α))
    (pins : List (α × Nat)) : List α → List (α × Nat) → Bool
  | [], _ => true
  | v :: rest, assign =>
    let colorOf := fun u => (assign.find? (·.1 == u)).map (·.2)
    let choices := match (pins.find? (·.1 == v)).map (·.2) with
      | some c => [c]
      | none => List.range k
    choices.any fun c =>
      if (adjTo edges v).any (fun u => colorOf u == some c) then false
      else colorableGoK k edges pins rest ((v, c) :: assign)

/-- Backtracking: does a proper `k`-coloring extend the pinned colors? -/
def colorableK {α : Type} [BEq α] (k : Nat) (edges : List (α × α))
    (verts : List α) (pins : List (α × Nat)) : Bool :=
  colorableGoK k edges pins verts []

end Atlas
