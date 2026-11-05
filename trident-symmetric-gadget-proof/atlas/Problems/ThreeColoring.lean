import atlas.Kits
/-!
  3-coloring as an atlas problem: only the constraint verifier lives here.

  The problem's constraint is proper 3-colorability. Its framework is the
  palette triangle G_T, G_F, G_B (three anchor parts, colors 0/1/2 pinned by
  position) with the G_B fan forced; an input pins the selected literal-role
  vertices to T and the forbidden ones to F, and the verifier answers whether
  a proper coloring extends the pins -- nothing else. The feasibility kit
  supplies the contract; colorability also serves as the monotone pruning
  bound (adding edges never makes a graph colorable).
-/

namespace Atlas

/-- The vertices adjacent to `v`. -/
def adjTo {α : Type} [BEq α] (edges : List (α × α)) (v : α) : List α :=
  edges.filterMap fun (a, b) =>
    if a == v then some b else if b == v then some a else none

/-- Backtracking kernel of `colorable`, total (structural on the remaining
    vertices) so that `atlas/ProofsPrune.lean` can prove it antitone in the
    edge set -- the property the search's viable pruning rests on. -/
def colorableGo {α : Type} [BEq α] (edges : List (α × α))
    (pins : List (α × Nat)) : List α → List (α × Nat) → Bool
  | [], _ => true
  | v :: rest, assign =>
    let colorOf := fun u => (assign.find? (·.1 == u)).map (·.2)
    let choices := match (pins.find? (·.1 == v)).map (·.2) with
      | some c => [c]
      | none => [0, 1, 2]
    choices.any fun c =>
      if (adjTo edges v).any (fun u => colorOf u == some c) then false
      else colorableGo edges pins rest ((v, c) :: assign)

/-- Backtracking: does a proper 3-coloring extend the pinned colors? -/
def colorable {α : Type} [BEq α] (edges : List (α × α)) (verts : List α)
    (pins : List (α × Nat)) : Bool :=
  colorableGo edges pins verts []

/-- The constraint under an input: anchors pinned to the palette (T, F, B in
    attach order), selected to T, forbidden to F. -/
def colorsOk {α : Type} [BEq α] (inst : Instance α) : Bool :=
  colorable inst.edges inst.verts <|
    inst.anchors.zip [0, 1, 2] ++
    inst.selected.map ((·, 0)) ++ inst.forbidden.map ((·, 1))

def threeColoring : Problem :=
  feasibility "3-coloring" colorsOk
    (attach := fun parts =>
      let a := fun p => Vertex.aux p 0
      let gt := parts.length
      ({ parts := parts ++ [1, 1, 1] },
       [(a gt, a (gt + 1)), (a (gt + 1), a (gt + 2)), (a (gt + 2), a gt),
        (.lit 0, a (gt + 2)), (.lit 1, a (gt + 2)), (.lit 2, a (gt + 2))]))
    (layer := fun n => (List.range n).flatMap fun v =>
      [(.pos v, .neg v), (.pos v, .anchor 2), (.neg v, .anchor 2)])
    (viable := colorsOk)

end Atlas
