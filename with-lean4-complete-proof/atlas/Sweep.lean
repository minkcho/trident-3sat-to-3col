import atlas.Problems.ThreeColoring
import atlas.Audit
import atlas.Report
import atlas.SliceOrder
/-!
  sweep: the exhaustive incremental search. Run with, e.g.,

    lake exe atlas-sweep three_coloring --max=6 --require-layer
    lake exe atlas-sweep three_coloring --max=3 --no-symmetry

  Starting from zero auxiliary vertices and growing to `--max=`, every slice
  is exhausted: with symmetry on (default), every orbit-type composition of
  the auxiliary budget and every subset of its edge orbits; with
  `--no-symmetry`, the raw space -- every subset of the individual edges over
  the same vertices, judged against all eight truth assignments (the
  four-class collapse is only sound for symmetric candidates).

  `--require-layer` keeps only compositions containing a size-3 or size-6
  orbit. This is the companion paper's degree-one-channel policy (its
  Lemma 12 proves layerless compositions carry no valid gadget), and it is
  what makes the symmetric sweep reach twelve vertices.

  Every slice reports leaves + pruned = total, so the accounting is exact:
  pruned subtrees are those in which a satisfiable row is already dead
  (the problem's monotone `viable` bound) -- and, in the orderly raw walk
  (`--no-symmetry` without `--no-canonical`), the branches cut by the
  relabeling check ([opus5.5 review] added).

  Within each budget the slices run cheapest first (ascending free-switch
  count, `orderSlices`): the most aggregated -- most symmetric -- slices
  have the smallest 2^K, so finds surface early, while the exhaustion, the
  found set and the accounting are unchanged by the order.
-/

namespace Atlas.Sweep

open Atlas

def parseNatFlag (pre : String) (fallback : Nat) (args : List String) : Nat :=
  match args.find? (·.startsWith pre) with
  | some arg => ((arg.drop pre.length).toNat?).getD fallback
  | none => fallback

def parseSizes (args : List String) : List Nat :=
  match args.find? (·.startsWith "--sizes=") with
  | some arg => ((arg.drop "--sizes=".length).toString.splitOn ",").filterMap (·.toNat?)
  | none => [1, 2, 3, 6]

def vname : Vertex → String
  | .lit i => s!"x{i}"
  | .aux p j => s!"a{p}.{j}"

def renderGraph (g : List Edge) : String :=
  ", ".intercalate <|
    (((g.map fun e => s!"{vname e.1}-{vname e.2}").toArray.qsort (· < ·))).toList

def withCommas (n : Nat) : String :=
  let rev := (toString n).toList.reverse
  String.ofList ((List.range rev.length).flatMap fun i =>
    (if 0 < i && i % 3 == 0 then [','] else []) ++ [rev.getD i ' ']).reverse

def runSlice (P : Problem) (stem : String) (parts : List Nat) (symmetry : Bool)
    (reportDir : String) (anchorNames : List String)
    (canonical : Bool) (shards shard : Nat) : IO Nat := do
  let t0 ← IO.monoMsNow
  let (U, stats) :=
    if symmetry then searchSlice P parts true shards shard
    else if canonical then searchSliceRaw P parts shards shard
    else searchSlice P parts false shards shard
  let t1 ← IO.monoMsNow
  let label := if symmetry then s!"parts={parts}" else s!"raw aux={parts.length}"
  IO.println s!"  [{label}] N={U.vertices.length}, candidates={withCommas stats.total} \
(leaves={withCommas stats.leaves}, pruned={withCommas stats.pruned}), \
found={stats.found.length}, {t1 - t0}ms"
  if stats.leaves + stats.pruned != stats.total then
    throw (IO.userError "accounting error: leaves + pruned != total")
  let partsTag := if symmetry then
    String.intercalate "-" (parts.map toString) else s!"raw{parts.length}"
  -- parallel shards share the report directory: name the shard
  let shardTag := if shards > 1 then s!"_s{shard}" else ""
  let mut idx := 0
  for (g, k) in stats.found do
    IO.println s!"    k={k}: {renderGraph g}"
    idx := idx + 1
    let path ← writeReport reportDir s!"{stem}_{partsTag}{shardTag}_{idx}" P parts g k
      symmetry anchorNames
    IO.println s!"    report: {path}"
  pure stats.found.length

/-- The registered problems: this cut carries 3-coloring only. -/
def problemFor : String → Option (Problem × List String)
  | "three_coloring" => some (threeColoring, ["G_T", "G_F", "G_B"])
  | _ => none

def problemNames : List String := ["three_coloring"]

/-- Every flag the sweep understands (prefix form). -/
def knownFlags : List String :=
  ["--max=", "--no-symmetry", "--require-layer", "--sizes=", "--report-dir=",
   "--no-canonical", "--shards=", "--shard="]

end Atlas.Sweep

open Atlas Atlas.Sweep in
def main (args : List String) : IO Unit := do
  let usage := s!"usage: atlas-sweep <{String.intercalate "|" problemNames}> \
[--max=N] [--no-symmetry] [--no-canonical] [--require-layer] [--sizes=1,2,3,6] \
[--report-dir=DIR] [--shards=S --shard=i]"
  let some (P, anchorNames) := args.head?.bind problemFor
    | throw (IO.userError usage)
  -- reject what would otherwise be ignored or silently defaulted
  -- [opus5.5 review] switches must match exactly (`--require-layers` or
  -- `--no-symmetry=1` passed the prefix test and were ignored), every
  -- `--sizes=` entry must parse, and a sharded run must name its shard
  for arg in args.drop 1 do
    if !(["--no-symmetry", "--require-layer", "--no-canonical"].contains arg ||
        (knownFlags.filter (·.endsWith "=")).any (fun pre => arg.startsWith pre)) then
      throw (IO.userError s!"unknown argument: {arg}\n{usage}")
  if let some arg := args.find? (·.startsWith "--sizes=") then
    if ((arg.drop "--sizes=".length).toString.splitOn ",").any (fun t => t.toNat?.isNone) then
      throw (IO.userError s!"--sizes= expects a comma-separated subset of 1,2,3,6, got: {arg}")
  if args.any (·.startsWith "--shards=") && !args.any (·.startsWith "--shard=") then
    throw (IO.userError "--shards= needs --shard=i (0 ≤ i < shards)")
  for pre in ["--max=", "--shards=", "--shard="] do
    if let some arg := args.find? (·.startsWith pre) then
      if ((arg.drop pre.length).toNat?).isNone then
        throw (IO.userError s!"{pre} expects a number, got: {arg}")
  let stem := args.headD "gadget"
  let maxAux := parseNatFlag "--max=" 4 args
  let symmetry := !args.contains "--no-symmetry"
  let requireLayer := args.contains "--require-layer"
  let sizes := parseSizes args
  if sizes.isEmpty || sizes.any (fun s => !([1, 2, 3, 6].contains s)) then
    throw (IO.userError "--sizes= expects a comma-separated subset of 1,2,3,6")
  let reportDir := match args.find? (·.startsWith "--report-dir=") with
    | some arg => (arg.drop "--report-dir=".length).toString
    | none => "atlas/reports"
  let canonical := !args.contains "--no-canonical"
  let shards := parseNatFlag "--shards=" 1 args
  let shard := parseNatFlag "--shard=" 0 args
  if shards > 1 && 2 ^ (Nat.log2 shards) != shards then
    throw (IO.userError "--shards must be a power of two")
  if shard ≥ shards then
    throw (IO.userError "--shard must be smaller than --shards")
  if !symmetry && P.negLayer.isSome then
    throw (IO.userError s!"{P.name} needs its negative-literal layer; \
the raw mode has no size-3 parts, so --no-symmetry is not supported here")
  let shardText := if shards > 1 then s!", shard {shard}/{shards}" else ""
  let canonText := if !symmetry && canonical then ", one per relabeling class" else ""
  IO.println s!"sweep: {P.name}, aux vertices 0..{maxAux}, \
symmetry={symmetry}{if requireLayer then ", layer-bearing compositions only" else ""}\
{if symmetry then ", cheapest slice first" else ""}\
{canonText}{shardText}"
  let mut total := 0
  for k in List.range (maxAux + 1) do
    IO.println s!"k = {k} auxiliary vertices:"
    let (slices, skipped) := slicesFor P.negLayer k sizes symmetry requireLayer
    -- the audit guard: whenever the independent partition count models this
    -- configuration (symmetric, no layer pre-filter), the enumeration must
    -- match it exactly -- a silent coverage gap kills the sweep here
    if symmetry && !requireLayer then
      let want := partitionCount k sizes
      let wantRun := if P.negLayer.isSome then partitionCountWith k sizes 3 else want
      if slices.length + skipped.length != want || slices.length != wantRun then
        throw (IO.userError s!"audit: slice enumeration mismatch at k={k}: \
ran {slices.length} + skipped {skipped.length}, expected {wantRun} + {want - wantRun}")
      IO.println s!"  (audit: {slices.length} + {skipped.length} slices, \
matches the partition count)"
    if !skipped.isEmpty then
      IO.println s!"  (skipped {skipped.length} composition(s): \
the negative-literal layer must be a size-3 part)"
    if slices.isEmpty then
      IO.println "  (no compositions)"
    for parts in orderSlices P slices symmetry do
      total := total +
        (← runSlice P stem parts symmetry reportDir anchorNames canonical shards shard)
  IO.println s!"sweep complete: {total} valid gadget(s) up to {maxAux} auxiliary vertices"
