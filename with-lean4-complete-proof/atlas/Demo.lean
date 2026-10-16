import atlas.Problems.ThreeColoring
/-!
  demo: reproduce the paper's search-space column, then rediscover gadgets
  and verify them at the formula level. Run with `lake exe atlas-demo`.

  Part 1 prints the census of the enumeration atlas for k = 4..7 auxiliary
  vertices; the totals are the "S3 orbit space" column of the paper's table.

  Part 2 hunts the two-layer slice at twelve vertices: the 3-coloring plugin
  finds exactly the trident (once per labeling of its two layers, budget 1).

  Part 3 checks the find on the two-clause micro-universe: the trident with
  k = 1.
-/

namespace Atlas.Demo

open Atlas

def withCommas (n : Nat) : String :=
  let rev := (toString n).toList.reverse
  let grouped := (List.range rev.length).flatMap fun i =>
    (if 0 < i && i % 3 == 0 then [','] else []) ++ [rev.getD i ' ']
  String.ofList grouped.reverse

def printCensus : IO Unit := do
  IO.println "the enumeration atlas, k = 4..7 (paper N = k + 6):"
  for k in [4, 5, 6, 7] do
    let rows := census k
    let line := " + ".intercalate (rows.map fun r => s!"2^{r.2.1}")
    let total := rows.foldl (fun acc r => acc + r.2.2) 0
    IO.println s!"  k={k}: {line} = {withCommas total}"
  let below := ((List.range 6).map orbitSpace).foldl (· + ·) 0
  IO.println s!"  cumulative k<6 (below twelve vertices): {withCommas below}\n"

def vertexName (U : Universe) (names : List String) : Vertex → String
  | .lit i => s!"x{i}"
  | .aux p j =>
    let base := names.getD p s!"s{p}"
    if U.size p > 1 then s!"{base}{j}" else base

def describe (U : Universe) (names : List String) (g : List Edge) : String :=
  let label := fun (e : Edge) =>
    let (a, b) := (vertexName U names e.1, vertexName U names e.2)
    if a ≤ b then s!"{a}-{b}" else s!"{b}-{a}"
  ", ".intercalate ((g.map label).toArray.qsort (· < ·)).toList

def runHunt (P : Problem) (parts : List Nat) (names : List String)
    (expect : Nat) : IO (List (List Edge × Nat)) := do
  let (U, found) := hunt P parts
  IO.println s!"{P.name} hunt in {repr U}"
  IO.println s!"  valid clause gadgets: {found.length}"
  for (g, k) in found do
    IO.println s!"    k={k}: {describe U names g}"
  if found.length != expect then
    throw (IO.userError s!"expected {expect} gadgets, found {found.length}")
  IO.println ""
  pure found

def runMulti (P : Problem) (parts : List Nat) (g : List Edge) : IO Unit := do
  match multiK P parts g with
  | some k => IO.println s!"  {P.name}: micro-universe passed, k = {k}"
  | none => throw (IO.userError s!"{P.name}: micro-universe check failed")

end Atlas.Demo

open Atlas Atlas.Demo in
def main : IO Unit := do
  printCensus
  let colHits ← runHunt threeColoring [3, 3] ["p", "u", "G_T", "G_F", "G_B"] (expect := 2)
  IO.println "multi-clause check on the micro-universe C1 = (x0 v x1 v x2), C2 = (~x0 v x1 v x3):"
  runMulti threeColoring [3, 3] (colHits.getD 0 ([], 0)).1
