import atlas.Problems.ThreeColoring
import atlas.Audit
import atlas.Assemble2
import atlas.Report
import atlas.Gadgets
import atlas.SliceOrder
/-!
  Tests for the atlas engine, the framework, and the 3-coloring plugin --
  the trident-only cut of the full line's Tests.lean. Run with
  `lake exe atlas-tests`.
-/

namespace Atlas.Tests

open Atlas

def check (name : String) (ok : Bool) : IO Unit := do
  if ok then IO.println s!"{name}: ok"
  else throw (IO.userError s!"{name}: FAILED")

-- known graphs (`tridentGraph` lives in atlas/Gadgets.lean) --------------------

def sortEdges (g : List Edge) : List (Nat × Nat) :=
  ((g.map fun e => (e.1.key, e.2.key)).toArray.qsort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))).toList

def sameGraph (g h : List Edge) : Bool := sortEdges g == sortEdges h

-- the engine -----------------------------------------------------------------

def testGroup : IO Unit := do
  check "group: six elements" (perms.eraseDups.length == 6)
  check "group: closure and parity" <| perms.all fun s => perms.all fun t =>
    perms.contains (compose s t) &&
    parity (compose s t) == (parity s + parity t) % 2

def testActions : IO Unit := do
  let U : Universe := { parts := [1, 2, 3, 6] }
  check "action: homomorphism" <| perms.all fun s => perms.all fun t =>
    U.vertices.all fun v => U.act (compose s t) v == U.act s (U.act t v)
  check "action: sign on size 2" (U.act (0,2,1) (.aux 1 0) == .aux 1 1)
  check "action: size 6 is free" <| perms.all fun s =>
    s == (0,1,2) || (List.range 6).all fun j => U.act s (.aux 3 j) != .aux 3 j

def testLiteralPairing : IO Unit := do
  -- a negative-literal layer moves in step with the literals: the SAME
  -- permutation table acts on both, so sigma carries the pair (x_i, ~x_i)
  -- to (x_sigma(i), ~x_sigma(i)) as a whole
  let U : Universe := { parts := [3] }
  check "pairing: lit and ~lit move together" <| perms.all fun s =>
    (List.range 3).all fun i =>
      U.act s (.lit i) == .lit (app s i) &&
      U.act s (.aux 0 i) == .aux 0 (app s i)
  -- hence the variable edges are one invariant switch: the matched orbit
  let orbit := U.edgeOrbit (normEdge (.lit 0, .aux 0 0))
  check "pairing: the variable edges form one invariant orbit"
    (orbit.length == 3 &&
     (List.range 3).all fun i => orbit.contains (normEdge (.lit i, .aux 0 i)))

def testOrbits : IO Unit := do
  let U : Universe := { parts := [1, 2, 3, 6] }
  let orbs := U.orbits
  check "orbits: partition the edges"
    ((orbs.map List.length).foldl (· + ·) 0 == U.edges.length &&
     U.edges.all fun e => orbs.any (·.contains e))
  check "orbits: closed under the action" <| orbs.all fun o =>
    o.all fun e => perms.all fun s => o.contains (U.actEdge s e)
  -- the pairwise orbit table, recovered by computation
  let counts := fun (parts : List Nat) => (Universe.orbits { parts }).length
  check "orbits: internal + literal per size"
    (counts [1] == 1 && counts [2] == 2 && counts [3] == 3 && counts [6] == 7)
  let cross := [([1,1], 1), ([1,2], 1), ([1,3], 1), ([1,6], 1), ([2,2], 2),
                ([2,3], 1), ([2,6], 2), ([3,3], 2), ([3,6], 3), ([6,6], 6)]
  check "orbits: cross table" <| cross.all fun (parts, want) =>
    counts parts == counts [parts.getD 0 0] + counts [parts.getD 1 0] + want

def testPaperNumbers : IO Unit := do
  check "paper: S3 orbit space k=4" (orbitSpace 4 == 1248)
  check "paper: S3 orbit space k=5" (orbitSpace 5 == 35648)
  check "paper: S3 orbit space k=6" (orbitSpace 6 == 2179968)
  check "paper: S3 orbit space k=7" (orbitSpace 7 == 273101312)
  check "paper: below twelve vertices"
    (((List.range 6).map orbitSpace).foldl (· + ·) 0 == 36999)
  check "paper: (3,0,1) has K = 12" ((Universe.orbits { parts := [1,1,1,3] }).length == 12)
  check "paper: free orbit has K = 7" ((Universe.orbits { parts := [6] }).length == 7)
  check "paper: two layers have K = 8" ((Universe.orbits { parts := [3,3] }).length == 8)

def testOrbitTypeOption : IO Unit := do
  check "sizes: {1,3} compositions at k=6"
    (compositions 6 [1, 3] == [[1,1,1,1,1,1], [1,1,1,3], [3,3]])
  check "sizes: {1,3} orbit space at k=6"
    (orbitSpace 6 [1, 3] == 2^21 + 2^12 + 2^8)
  check "sizes: {3} orbit space at k=6" (orbitSpace 6 [3] == 2^8)

def testSymmetryOff : IO Unit := do
  let U : Universe := { parts := [1] }
  check "symmetry: on/off counts" (U.count == 2 && U.count (symmetry := false) == 8)
  let sym := U.graphs
  let raw := U.graphs (symmetry := false)
  check "symmetry: quotient is a subset of the raw walk"
    (sym.length == 2 && raw.length == 8 &&
     sym.all fun g => raw.any (sameGraph g))
  -- the audit upgrade: not just a subset -- the quotient IS the invariant
  -- part of the raw walk (set equality, so nothing invariant is missed)
  check "symmetry: quotient equals the invariant raw graphs ([1] and [2])"
    (([[1], [2]] : List (List Nat)).all fun parts =>
      let V : Universe := { parts }
      let symV := V.graphs
      let inv := (V.graphs (symmetry := false)).filter (invariantUnder V)
      symV.length == inv.length && symV.all fun g => inv.any (sameGraph g))

def testForced : IO Unit := do
  let U : Universe := { parts := [3] }
  let matched := (Vertex.lit 0, Vertex.aux 0 0)
  check "forced: orbit stays on" <|
    let gs := U.graphs (forced := [matched])
    gs.length == 4 && gs.all fun g =>
      (List.range 3).all fun i => g.contains (normEdge (.lit i, .aux 0 i))

def testGadgetChecks : IO Unit := do
  check "3col: the trident is a gadget with k = 1"
    (gadgetK threeColoring [3, 3] (tridentGraph 0 1 2 3 4) == some 1)
  check "3col: the framework alone is not" <|
    let (U, forced) := threeColoring.attach [3, 3]
    gadgetK threeColoring [3, 3] (U.splitForced forced).1 == none

def testHunts : IO Unit := do
  let (_, hits) := hunt threeColoring [3, 3]
  check "hunt: 3-coloring finds exactly the trident, once per layer labeling, with k = 1"
    (hits.length == 2 && hits.all (·.2 == 1) &&
     hits.any (fun h => sameGraph h.1 (tridentGraph 0 1 2 3 4)) &&
     hits.any (fun h => sameGraph h.1 (tridentGraph 1 0 2 3 4)))

/-- The textbook OR-chain clause gadget (companion paper Fig. 1(c)): five
    auxiliary singletons a0..a4, ten gadget edges, anchors appended by attach
    as parts 5 (G_T), 6 (G_F), 7 (G_B). -/
def orChain : List Edge :=
  let a := fun (p : Nat) => Vertex.aux p 0
  ([(a 5, a 6), (a 6, a 7), (a 7, a 5)] ++
   (List.range 3).map (fun i => (Vertex.lit i, a 7)) ++
   [(Vertex.lit 0, a 0), (Vertex.lit 1, a 1), (a 0, a 1),
    (a 0, a 2), (a 1, a 2), (a 2, a 3), (Vertex.lit 2, a 4),
    (a 3, a 4), (a 3, a 5), (a 4, a 5)]).map normEdge

def testTextbook : IO Unit := do
  -- asymmetric candidates must face all eight assignments, not four classes
  check "textbook: the OR-chain passes the eight-row check with k = 1"
    (gadgetK threeColoring [1, 1, 1, 1, 1] orChain (symmetry := false) == some 1)
  let (uo, _) := threeColoring.attach [1, 1, 1, 1, 1]
  check "textbook: the OR-chain is not S3-invariant" <| perms.any fun s =>
    !sameGraph (orChain.map fun e => normEdge (uo.act s e.1, uo.act s e.2)) orChain

def testSearchSlice : IO Unit := do
  let (_, stats) := searchSlice threeColoring []
  check "slice: exact accounting at k = 0 (symmetric)"
    (stats.leaves + stats.pruned == stats.total && stats.found.isEmpty)
  let (_, statsOff) := searchSlice threeColoring [] (symmetry := false)
  check "slice: exact accounting at k = 0 (raw)"
    (statsOff.leaves + statsOff.pruned == statsOff.total && statsOff.found.isEmpty)

def testShards : IO Unit := do
  let mut found := 0
  let mut totals := 0
  for i in List.range 4 do
    let (_, stats) := searchSlice threeColoring [3, 3] true 4 i
    found := found + stats.found.length
    totals := totals + stats.total
  check "shards: the four shards partition the slice and its finds"
    (found == 2 && totals == 65536)

def testCanonicalRaw : IO Unit := do
  let (_, plain) := searchSlice threeColoring [1, 1] false
  let (_, canon) := searchSliceRaw threeColoring [1, 1]
  check "canonical raw: same verdict, exact accounting, fewer branches"
    (plain.found.length == 0 && canon.found.length == 0 &&
     canon.total == plain.total &&
     canon.leaves + canon.pruned == canon.total &&
     canon.leaves ≤ plain.leaves)

def testReport : IO Unit := do
  let tex := latexReport threeColoring [3, 3] (tridentGraph 0 1 2 3 4) 1
    (anchorNames := ["G_T", "G_F", "G_B"])
  check "report: standalone LaTeX with figure and both tables"
    (tex.startsWith "\\documentclass" &&
     (tex.splitOn "\\begin{tikzpicture}").length == 2 &&
     (tex.splitOn "G_T").length >= 2 &&
     (tex.splitOn "\\bottomrule").length == 3 &&
     (tex.splitOn "passed with $k = 1$").length == 2)

def sortNat (c : List Nat) : List Nat := (c.toArray.qsort (· < ·)).toList

/-- The definitional oracle for a slice: every graph of the universe judged
    by gadgetK -- no walk, no pruning -- compared with searchSlice's finds. -/
def oracleMatch (P : Problem) (parts : List Nat) : Bool :=
  let (U, forced) := P.attach parts
  let oracle := (U.graphs (forced := forced)).filterMap fun g =>
    (gadgetK P parts g).map fun k => (sortEdges g, k)
  let found := (hunt P parts).2.map fun (g, k) => (sortEdges g, k)
  found.length == oracle.length && found.all oracle.contains &&
  oracle.all found.contains

def testAudit : IO Unit := do
  -- 1. enumeration counts against the independent partition DP, with
  --    hand-computed anchors (k=6: 8 partitions of which 3 contain a 3 --
  --    exactly the ran+skipped split of the recorded sweeps)
  check "audit: composition counts match the partition DP (k <= 8)"
    ((List.range 9).all fun k =>
      ([[1, 2, 3, 6], [1, 3], [3]] : List (List Nat)).all fun s =>
        (compositions k s).length == partitionCount k s)
  check "audit: hand anchors at k = 6 and k = 7"
    (partitionCount 6 == 8 && partitionCountWith 6 [1, 2, 3, 6] 3 == 3 &&
     partitionCount 7 == 9 && partitionCountWith 7 [1, 2, 3, 6] 3 == 4)
  -- 2. slice-selection soundness: the properties whose violation was the
  --    coverage bug (the old positional filter dies on the first line)
  check "audit: slice selection is sound and multiset-preserving (k <= 8)"
    ((List.range 9).all fun k =>
      let gen := compositions k
      let (run, skipped) := slicesFor (some 0) k [1, 2, 3, 6] true false
      skipped.all (fun c => !c.contains 3) &&
      run.all (fun c => c.getD 0 0 == 3) &&
      run.map sortNat == gen.filter (·.contains 3) &&
      run.length + skipped.length == gen.length &&
      run.length == partitionCountWith k [1, 2, 3, 6] 3)
  -- 3. small-k brute force: every ordered tuple, deduplicated by sorting,
  --    equals the composition list as a set (catches compensating errors
  --    that a bare count comparison cannot)
  check "audit: compositions equal the deduplicated brute force (k <= 5)"
    ((List.range 6).all fun k =>
      let brute := ((allTuples k).map sortNat).eraseDups
      let comp := compositions k
      brute.length == comp.length && comp.all brute.contains &&
      brute.all comp.contains)
  -- 4. the pruned walk against the definitional enumeration; 3COL is the
  --    one problem whose viable bound actually prunes, so its slice is the
  --    live test of pruning soundness (the antitonicity theorem is
  --    ProofsPrune.colorsOk_antitone; this check is its empirical twin)
  check "audit: the pruning walk matches the oracle where pruning is active"
    (oracleMatch threeColoring [3, 3])

def testAssembler2 : IO Unit := do
  -- the subsumption (taxonomy row 1): Phase 1 is the by-literal quotient
  -- of the general assembler and reproduces assemble verbatim
  check "asm2: phase1Assemble reproduces assemble verbatim (3COL)"
    (phase1Assemble threeColoring [3, 3] (tridentGraph 0 1 2 3 4) microUniverse
       == assemble threeColoring [3, 3] (tridentGraph 0 1 2 3 4) microUniverse)

def testSliceOrder : IO Unit := do
  -- cheapest-first slice order: a permutation of the enumeration with
  -- non-decreasing free-switch counts; the most aggregated slice leads
  let (slices, _) := slicesFor none 4 [1, 2, 3, 6] true false
  let ordered := orderSlices threeColoring slices
  check "order: a permutation of the enumeration"
    (ordered.length == slices.length && slices.all (ordered.contains ·) &&
     ordered.all (slices.contains ·))
  check "order: free-switch counts are non-decreasing" <|
    let costs := ordered.map fun parts => sliceCost threeColoring parts
    (costs.zip (costs.drop 1)).all fun (a, b) => a ≤ b
  check "order: [3] leads the k = 3 slices" <|
    let (s3, _) := slicesFor none 3 [1, 2, 3, 6] true false
    (orderSlices threeColoring s3).headD [] == [3]

def testMultiClause : IO Unit := do
  check "multi: trident passes the micro-universe with k = 1"
    (multiK threeColoring [3, 3] (tridentGraph 0 1 2 3 4) == some 1)
  -- the interface limit of Sect. 3.2 of the paper: the rows pin both literal
  -- polarities, so they cannot see a missing literal-layer gadget; that gap
  -- is closed by the assembly theorem, not by the table
  check "multi: the table cannot see a missing literal layer"
    (multiK { threeColoring with layer := fun _ => [] } [3, 3]
      (tridentGraph 0 1 2 3 4) == some 1)

end Atlas.Tests


def main : IO Unit := do
  Atlas.Tests.testGroup
  Atlas.Tests.testActions
  Atlas.Tests.testLiteralPairing
  Atlas.Tests.testOrbits
  Atlas.Tests.testPaperNumbers
  Atlas.Tests.testOrbitTypeOption
  Atlas.Tests.testSymmetryOff
  Atlas.Tests.testForced
  Atlas.Tests.testGadgetChecks
  Atlas.Tests.testHunts
  Atlas.Tests.testTextbook
  Atlas.Tests.testSearchSlice
  Atlas.Tests.testShards
  Atlas.Tests.testCanonicalRaw
  Atlas.Tests.testAudit
  Atlas.Tests.testAssembler2
  Atlas.Tests.testSliceOrder
  Atlas.Tests.testReport
  Atlas.Tests.testMultiClause
  IO.println "all tests passed"
