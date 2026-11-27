import proof.TridentGadget
import search.Space

/-!
  The trident in the candidate space.

  In the candidate space of the composition `[3, 3]` the trident appears
  under two labelings: the branch layer on part 0 and the upper triangle on
  part 1 (`tridentA`), or the other way round (`tridentB`). The maps `toTVA`
  and `toTVB` send the vertices of the candidate space to the vertices of
  the trident graph of `Definition1.lean`, and the edge lists are compared
  with that graph pair by pair.
-/

namespace Atlas

/-- The trident with the branch layer on part 0 and the upper triangle on
    part 1. -/
def tridentA : List Edge :=
  [(.aux 1 0, .aux 1 1), (.aux 1 0, .aux 1 2), (.aux 1 1, .aux 1 2),
   (.aux 0 0, .aux 2 0), (.aux 0 1, .aux 2 0), (.aux 0 2, .aux 2 0),
   (.aux 0 0, .aux 1 0), (.aux 0 1, .aux 1 1), (.aux 0 2, .aux 1 2),
   (.lit 0, .aux 0 0), (.lit 1, .aux 0 1), (.lit 2, .aux 0 2),
   (.lit 0, .aux 4 0), (.lit 1, .aux 4 0), (.lit 2, .aux 4 0),
   (.aux 2 0, .aux 3 0), (.aux 2 0, .aux 4 0), (.aux 3 0, .aux 4 0)]

/-- The trident with the two layers exchanged: the branch layer on part 1
    and the upper triangle on part 0. -/
def tridentB : List Edge :=
  [(.aux 1 0, .aux 2 0), (.aux 1 1, .aux 2 0), (.aux 1 2, .aux 2 0),
   (.aux 0 0, .aux 1 0), (.aux 0 1, .aux 1 1), (.aux 0 2, .aux 1 2),
   (.aux 0 0, .aux 0 1), (.aux 0 0, .aux 0 2), (.aux 0 1, .aux 0 2),
   (.lit 0, .aux 1 0), (.lit 1, .aux 1 1), (.lit 2, .aux 1 2),
   (.lit 0, .aux 4 0), (.lit 1, .aux 4 0), (.lit 2, .aux 4 0),
   (.aux 2 0, .aux 3 0), (.aux 2 0, .aux 4 0), (.aux 3 0, .aux 4 0)]

end Atlas

namespace Def1

open Atlas

/-- The index `j` as an element of `Fin 3`. -/
def idx (j : Nat) : Fin 3 := ⟨j % 3, Nat.mod_lt j (by decide)⟩

theorem idx_val (i : Fin 3) : idx i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem idx_of_lt {i : Nat} (hi : i < 3) : idx i = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)

/-- The vertices of the candidate space of `[3, 3]` as vertices of the
    trident, for the labeling `tridentA`: part 0 holds the branch vertices
    and part 1 the upper triangle. -/
def toTVA : Vertex → TV
  | .lit i => .x (idx i)
  | .aux 0 j => .p (idx j)
  | .aux 1 j => .u (idx j)
  | .aux 2 _ => .gT
  | .aux 3 _ => .gF
  | .aux _ _ => .gB

/-- The same for the labeling `tridentB`: part 1 holds the branch vertices
    and part 0 the upper triangle. -/
def toTVB : Vertex → TV
  | .lit i => .x (idx i)
  | .aux 0 j => .u (idx j)
  | .aux 1 j => .p (idx j)
  | .aux 2 _ => .gT
  | .aux 3 _ => .gF
  | .aux _ _ => .gB

/-- Check of data: the edge list `tridentA` of the engine is the trident
    graph of `Definition1.lean`, pair by pair. -/
theorem toTVA_adj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
    ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices,
      (normEdge (a, b) ∈ tridentA ↔ trident.Adj (toTVA a) (toTVA b)) := by
  decide

theorem toTVB_adj : ∀ a ∈ (threeColoring.attach [3, 3]).1.vertices,
    ∀ b ∈ (threeColoring.attach [3, 3]).1.vertices,
      (normEdge (a, b) ∈ tridentB ↔ trident.Adj (toTVB a) (toTVB b)) := by
  decide

end Def1

namespace Atlas.Statement

open Atlas

/-- Check of data: the two edge lists are S3-symmetric candidates of the
    composition `[3, 3]`. -/
theorem tridentA_tridentB_symmetric :
    SymCandidate [3, 3] tridentA ∧ SymCandidate [3, 3] tridentB := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> decide

/-- Check of data: the judge accepts the two edge lists on all eight
    inputs. -/
theorem tridentA_tridentB_valid :
    gadgetK threeColoring [3, 3] tridentA false = some 1 ∧
    gadgetK threeColoring [3, 3] tridentB false = some 1 := by
  decide

end Atlas.Statement
