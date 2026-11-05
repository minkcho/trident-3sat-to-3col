import atlas.Framework
/-!
  kits : problem constructors over the Framework. This cut keeps the one
  kit 3-coloring uses -- `feasibility`, "a solution exists under pins":
  the objective is 1/0 and the budget is 1 -- and the mask enumeration
  `bitSubset` the proof layer reflects. (The full line also has the
  minSubset / maxSubset / maxObjective kits of the other problems.)
-/

namespace Atlas

/-- The subset of `rest` selected by the bits of `mask`: the head is taken
    iff bit 0 is set, the tail is decided by the shifted mask. Written as a
    structural recursion so that `atlas/ProofsKits.lean` can prove the
    enumeration sound (a masked subset is a sublist) and complete (every
    sublist is some mask's subset below 2^length). -/
def bitSubset {α : Type} (mask : Nat) : List α → List α
  | [] => []
  | v :: rest =>
    (if mask &&& 1 == 1 then [v] else []) ++ bitSubset (mask >>> 1) rest

/-- Feasibility kit: a single satisfaction predicate under the input's pins;
    the objective is 1/0 and the budget is 1. -/
def feasibility (name : String)
    (ok : {α : Type} → [BEq α] → Instance α → Bool)
    (attach : List Nat → Universe × List Edge)
    (layer : Nat → List MEdge := fun _ => [])
    (viable : {α : Type} → [BEq α] → Instance α → Bool := fun _ => true) :
    Problem where
  name := name
  attach := attach
  layer := layer
  measure := fun inst => some (if ok inst then 1 else 0)
  exact := fun inst k => k == 1 && ok inst
  target := fun isSat k actual => if isSat then k ≤ actual else actual < k
  viable := viable

end Atlas
