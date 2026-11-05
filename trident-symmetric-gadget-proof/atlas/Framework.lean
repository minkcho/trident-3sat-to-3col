import atlas.Atlas
/-!
  framework : the generic verification pipeline over the atlas engine.

  The engine generates candidate graphs and knows nothing about any target
  problem; a `Problem` packages only what one target must know -- its
  framework (anchor parts, forced edges) and its constraint verifier, which
  judges a graph under one input and nothing more. Everything else is generic
  and lives here: the four gadget input classes, the budget read off the table
  (threshold separation), the faithful column, the hunt, and the multi-clause
  check that assembles clause copies on a shared literal layer and runs the
  full 2^n-row table.

  The verifier is polymorphic in the vertex type, so a single definition
  judges both the local gadget and the assembled multi-clause graph.
-/

namespace Atlas

/-- What the framework hands a verifier: the graph and the whole input state.
    `anchors` are the vertices of the parts `attach` appended, in order;
    `selected`/`forbidden` are the literal-role vertices the input forces
    true/false. -/
structure Instance (α : Type) where
  verts : List α
  edges : List (α × α)
  anchors : List α
  selected : List α
  forbidden : List α

/-- The shared literal layer and the clause copies of the multi-clause graph. -/
inductive MVertex
  | pos (v : Nat)             -- literal-layer vertex x_v
  | neg (v : Nat)             -- literal-layer vertex ~x_v
  | anchor (p : Nat)          -- shared anchor (attach-appended part p)
  | aux (c p j : Nat)         -- clause c's copy of auxiliary vertex (p, j)
deriving Repr, DecidableEq, Inhabited

abbrev MEdge := MVertex × MVertex

def MVertex.enc : MVertex → Nat
  | .pos v => 2 * v
  | .neg v => 2 * v + 1
  | .anchor p => 100000 + p
  | .aux c p j => 200000 + (c * 100 + p) * 100 + j

def normM (e : MEdge) : MEdge :=
  if e.1.enc ≤ e.2.enc then e else (e.2, e.1)

/-- A target problem: its framework and its constraint verifier.

    `measure` is the problem's objective κ under an input (the target column);
    `exact` asks whether the budget k is realized in agreement with the input
    (the faithful column); `target` is the threshold form relating the budget
    to a row's objective. `negLayer` names the auxiliary layer realizing the
    negative literals, when the gadget carries one; `layer` is the
    per-variable literal-layer gadget added at multi-clause assembly. -/
structure Problem where
  name : String
  attach : List Nat → Universe × List Edge
  negLayer : Option Nat := none
  layer : (varCount : Nat) → List MEdge := fun _ => []
  measure : {α : Type} → [BEq α] → Instance α → Option Nat
  exact : {α : Type} → [BEq α] → Instance α → Nat → Bool
  target : Bool → Nat → Nat → Bool
  /-- Monotone viability of a partial graph on a satisfiable row: may a
      supergraph still pass? Used to prune the search; must be antitone in
      the edge set (3-coloring: the row must still be colorable). -/
  viable : {α : Type} → [BEq α] → Instance α → Bool := fun _ => true

-- ------------------------------------------------- the generic budget logic

/-- Read the budget off a table of (isSat, instance) rows: every satisfiable
    row must realize one common objective value k, every row must pass the
    threshold against k, and the faithful column must agree with the row.
    Rows are checked in order and the first failure stops the scan. -/
def commonK (P : Problem) {α : Type} [BEq α]
    (rows : List (Bool × Instance α)) : Option Nat := do
  let k ← rows.findSome? fun (isSat, inst) => if isSat then P.measure inst else none
  if rows.all fun (isSat, inst) =>
       (match P.measure inst with
        | some a => (!isSat || a == k) && P.target isSat k a
        | none => false) &&
       P.exact inst k == isSat then
    some k
  else
    none

-- --------------------------------------------------- the gadget-level check

/-- The literal sides under an assignment (bit i of `env` = literal i true):
    the true side of every literal role is selected, the false side
    forbidden. With a negative layer the false side of variable i is its
    layer vertex; without one it is the literal vertex itself. -/
def envSidesGadget (P : Problem) (env : Nat) : List Vertex × List Vertex :=
  match P.negLayer with
  | some neg =>
    ((List.range 3).map fun i => if env >>> i &&& 1 == 1 then .lit i else .aux neg i,
     (List.range 3).map fun i => if env >>> i &&& 1 == 1 then .aux neg i else .lit i)
  | none =>
    ((List.range 3).filterMap fun i =>
       if env >>> i &&& 1 == 1 then some (.lit i) else none,
     (List.range 3).filterMap fun i =>
       if env >>> i &&& 1 == 1 then none else some (.lit i))

/-- Symmetric candidates collapse the eight assignments into four classes by
    the number of true literals; asymmetric candidates must face all eight. -/
def gadgetEnvs (symmetry : Bool) : List Nat :=
  if symmetry then [0, 1, 3, 7] else List.range 8

def anchorsOf (own : Nat) (U : Universe) : List Vertex :=
  (List.range (U.parts.length - own)).map fun d => Vertex.aux (own + d) 0

def gadgetRows (P : Problem) (symmetry : Bool) :
    List (Bool × List Vertex × List Vertex) :=
  (gadgetEnvs symmetry).map fun env =>
    let (sel, forb) := envSidesGadget P env
    (env != 0, sel, forb)

def checkGadget (P : Problem) (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex)) (g : List Edge) : Option Nat :=
  commonK P <| rows.map fun (isSat, sel, forb) =>
    (isSat, { verts := U.vertices, edges := g, anchors,
              selected := sel, forbidden := forb })

/-- A declared negative-literal layer must be a size-3 part: a smaller part
    makes the framework reference pair vertices that do not exist (phantom
    references, inflating every objective by a row-dependent amount), and the
    sign or regular action of sizes 2 and 6 would break the literal pairing
    that the class collapse and the multi-clause assembly rely on. -/
def negLayerOk (P : Problem) (U : Universe) : Bool :=
  match P.negLayer with
  | some p => U.size p == 3
  | none => true

/-- Is `g` a clause gadget for `P`? Returns the derived budget when the table
    separates and is faithful. -/
def gadgetK (P : Problem) (parts : List Nat) (g : List Edge)
    (symmetry : Bool := true) : Option Nat :=
  let (U, _) := P.attach parts
  if !negLayerOk P U then none
  else checkGadget P U (anchorsOf parts.length U) (gadgetRows P symmetry) g

-- ------------------------------------------------------- the pruned search

structure SliceStats where
  found : List (List Edge × Nat) := []
  leaves : Nat := 0
  pruned : Nat := 0
  total : Nat := 0

/-- Prune only where a subtree is worth killing. -/
def pruneDepth : Nat := 8

def searchAux (P : Problem) (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex))
    (free : List (List Edge)) (acc : List Edge) (stats : SliceStats) : SliceStats :=
  match free with
  | [] =>
    let stats := { stats with leaves := stats.leaves + 1 }
    match checkGadget P U anchors rows acc with
    | some k => { stats with found := (acc, k) :: stats.found }
    | none => stats
  | g :: rest =>
    let withG := g ++ acc
    let alive := rest.length < pruneDepth ||
      rows.all fun (isSat, sel, forb) =>
        !isSat || P.viable { verts := U.vertices, edges := withG, anchors,
                             selected := sel, forbidden := forb }
    let stats :=
      if alive then
        searchAux P U anchors rows rest withG stats
      else
        { stats with pruned := stats.pruned + 2 ^ rest.length }
    searchAux P U anchors rows rest acc stats

/-- Pre-decide the first log2(shards) free switches according to the shard
    index (bit j of `shard` decides switch j: on merges into the base, off is
    dropped). The shards partition the slice exactly. -/
def shardSplit (base : List Edge) (free : List (List Edge))
    (shards shard : Nat) : List Edge × List (List Edge) :=
  let bits := Nat.min (Nat.log2 shards) free.length
  let base := ((List.range bits).zip (free.take bits)).foldl (init := base)
    fun b (j, g) => if shard >>> j &&& 1 == 1 then g ++ b else b
  (base, free.drop bits)

/-- Exhaust one slice of the atlas: every candidate over `parts` (the orbit
    quotient with symmetry on, the raw space with symmetry off; the row set
    matches -- four classes against symmetric candidates, all eight
    assignments otherwise). `leaves + pruned = total` accounts for every
    candidate. -/
def searchSlice (P : Problem) (parts : List Nat)
    (symmetry : Bool := true) (shards : Nat := 1) (shard : Nat := 0) :
    Universe × SliceStats :=
  let (U, forced) := P.attach parts
  if !negLayerOk P U then (U, {}) else
  let (base, free) := U.splitForced forced symmetry
  -- a shard index beyond the slice's own switches names an empty part, so
  -- the shards partition every slice exactly (a small-k slice of a sharded
  -- sweep has fewer switches than log2 shards)
  if 1 < shards && shard >>> Nat.min (Nat.log2 shards) free.length != 0 then (U, {}) else
  let (base, free) :=
    if shards ≤ 1 then (base, free) else shardSplit base free shards shard
  let anchors := anchorsOf parts.length U
  let rows := gadgetRows P symmetry
  let stats := searchAux P U anchors rows free base { total := 2 ^ free.length }
  (U, { stats with found := stats.found.reverse })

-- ------------------------------------ the raw walk, one per relabeling class

/-- In the raw space the auxiliary vertices are interchangeable: the verifier
    never names them (literals are pinned by the input, anchors by their
    colors, auxiliaries are anonymous), so relabeling auxiliaries preserves
    the whole table. The orderly walk therefore decides the framework
    attachments of aux 0, then aux 1, ..., and keeps a branch only while the
    attachment profiles are non-decreasing. Sorting the profiles of any graph
    is such a relabeling, so at least one representative of every relabeling
    class survives -- nothing is lost up to isomorphism -- while most
    duplicates are never built. Proved for 3-coloring in
    `atlas/ProofsRawWalk.lean` (`searchSliceRaw_complete_threeColoring`). -/

def rawFramework (own : Nat) (U : Universe) : List Vertex :=
  (List.range 3).map .lit ++ anchorsOf own U

def rawProfile (fw : List Vertex) (g : List Edge) (v : Vertex) : Nat :=
  ((List.range fw.length).zip fw).foldl (init := 0) fun m (j, w) =>
    if g.contains (normEdge (v, w)) then m + 2 ^ j else m

/-- The raw switches reordered for the orderly walk: framework-framework
    edges, then the framework attachments of each auxiliary vertex in turn
    (the last edge of each group carries the group index as a boundary
    marker), then the auxiliary-auxiliary edges. -/
def rawOrderedSwitches (own : Nat) (U : Universe) (free : List (List Edge)) :
    List (Edge × Option Nat) :=
  let es := free.flatMap id
  let fw := rawFramework own U
  let auxIdx : Vertex → Option Nat := fun v => match v with
    | .aux p _ => if p < own then some p else none
    | _ => none
  let isFw := fun (v : Vertex) => fw.contains v
  let fwfw := es.filter fun e => isFw e.1 && isFw e.2
  let internal := es.filter fun e => (auxIdx e.1).isSome && (auxIdx e.2).isSome
  let groups := (List.range own).flatMap fun i =>
    let ext := es.filter fun e =>
      (auxIdx e.1 == some i && isFw e.2) || (auxIdx e.2 == some i && isFw e.1)
    match ext.reverse with
    | [] => []
    | last :: front => front.reverse.map ((·, none)) ++ [(last, some i)]
  fwfw.map ((·, none)) ++ groups ++ internal.map ((·, none))

def searchRawAux (P : Problem) (U : Universe) (anchors : List Vertex)
    (rows : List (Bool × List Vertex × List Vertex)) (fw : List Vertex)
    (remaining : List (Edge × Option Nat)) (prescribe : List Bool)
    (acc : List Edge) (stats : SliceStats) : SliceStats :=
  match remaining with
  | [] =>
    let stats := { stats with leaves := stats.leaves + 1 }
    match checkGadget P U anchors rows acc with
    | some k => { stats with found := (acc, k) :: stats.found }
    | none => stats
  | (e, mark) :: rest =>
    let subtree := fun (ps : List Bool) => 2 ^ (rest.length - Nat.min ps.length rest.length)
    let branch := fun (acc' : List Edge) (ps : List Bool) (stats : SliceStats) =>
      let sorted := match mark with
        | some i => i == 0 ||
            rawProfile fw acc' (.aux (i - 1) 0) ≤ rawProfile fw acc' (.aux i 0)
        | none => true
      if !sorted then { stats with pruned := stats.pruned + subtree ps }
      else searchRawAux P U anchors rows fw rest ps acc' stats
    match prescribe with
    | b :: ps => branch (if b then e :: acc else acc) ps stats
    | [] =>
      let withAcc := e :: acc
      let alive := rest.length < pruneDepth ||
        rows.all fun (isSat, sel, forb) =>
          !isSat || P.viable { verts := U.vertices, edges := withAcc, anchors,
                               selected := sel, forbidden := forb }
      let stats :=
        if alive then branch withAcc [] stats
        else { stats with pruned := stats.pruned + subtree [] }
      branch acc [] stats

/-- Exhaust the raw slice one auxiliary-relabeling class at a time (at least
    one representative of every class; usually exactly one). -/
def searchSliceRaw (P : Problem) (parts : List Nat)
    (shards : Nat := 1) (shard : Nat := 0) : Universe × SliceStats :=
  let (U, forced) := P.attach parts
  if !negLayerOk P U then (U, {}) else
  let (base, free) := U.splitForced forced false
  let tagged := rawOrderedSwitches parts.length U free
  let bits := Nat.min (Nat.log2 shards) tagged.length
  if 1 < shards && shard >>> bits != 0 then (U, {}) else
  let prescribe := (List.range bits).map fun j => shard >>> j &&& 1 == 1
  let anchors := anchorsOf parts.length U
  -- `total` counts the free switches themselves, not the reordered list:
  -- should the reordering ever drop a switch (it keeps only attachments to
  -- size-1 framework parts; every registered problem has such anchors),
  -- the sweep's accounting guard `leaves + pruned = total` fails loudly
  -- instead of silently walking a smaller space
  let stats := searchRawAux P U anchors (gadgetRows P false)
    (rawFramework parts.length U) tagged prescribe base
    { total := 2 ^ (free.length - bits) }
  (U, { stats with found := stats.found.reverse })

/-- Attach the problem's framework to the parts and return every valid clause
    gadget in that slice of the atlas, with its derived budget. -/
def hunt (P : Problem) (parts : List Nat) : Universe × List (List Edge × Nat) :=
  let (U, stats) := searchSlice P parts
  (U, stats.found)

-- ---------------------------------------------------- the multi-clause check

abbrev ClauseSpec := List (Nat × Bool)

/-- The two-clause micro-universe C1 = (x0 v x1 v x2), C2 = (~x0 v x1 v x3):
    one representative of every cross-clause literal relation. -/
def microUniverse : List ClauseSpec :=
  [[(0, true), (1, true), (2, true)], [(0, false), (1, true), (3, true)]]

def varCount (clauses : List ClauseSpec) : Nat :=
  clauses.foldl (fun acc c => c.foldl (fun m l => Nat.max m (l.1 + 1)) acc) 0

def litVertex (l : Nat × Bool) : MVertex := if l.2 then .pos l.1 else .neg l.1
def negLitVertex (l : Nat × Bool) : MVertex := if l.2 then .neg l.1 else .pos l.1

/-- Map one gadget vertex into clause c's copy: literal ports onto the
    clause's literals in the shared layer, the negative layer onto the
    opposite polarity, attach-appended parts onto shared anchors, and
    everything else onto fresh clause-local vertices. -/
-- [opus5.5 review] a clause shorter than three literals wires its missing
-- ports to x0 through `getD` (open item M6, History.md); every theorem
-- assumes length-3 clauses. Left unchanged: the proof layer unfolds this.
def mapVertex (P : Problem) (own c : Nat) (clause : ClauseSpec) : Vertex → MVertex
  | .lit i => litVertex (clause.getD i (0, true))
  | .aux p j =>
    if p ≥ own then .anchor (p - own)
    else if P.negLayer == some p then negLitVertex (clause.getD j (0, true))
    else .aux c p j

/-- Assemble the multi-clause graph: one copy of the gadget per clause on the
    shared literal layer, unioned with the problem's literal-layer gadget. -/
def assemble (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) : List MVertex × List MEdge :=
  let own := parts.length
  let n := varCount clauses
  let copies := ((List.range clauses.length).zip clauses).flatMap fun (c, clause) =>
    g.map fun e => normM (mapVertex P own c clause e.1, mapVertex P own c clause e.2)
  let edges := (copies ++ (P.layer n).map normM).eraseDups.filter fun e => e.1 != e.2
  let layerVerts := (List.range n).flatMap fun v => [MVertex.pos v, MVertex.neg v]
  ((layerVerts ++ edges.flatMap fun e => [e.1, e.2]).eraseDups, edges)

def formulaSat (env : Nat) (clauses : List ClauseSpec) : Bool :=
  clauses.all fun c => c.any fun l => (env >>> l.1 &&& 1 == 1) == l.2

/-- Is `g` a clause gadget for `P` at the formula level? Assembles the
    clauses and reads the budget off the full 2^n-row table. -/
def multiK (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec := microUniverse) : Option Nat :=
  let (U, _) := P.attach parts
  if !negLayerOk P U then none else
  let anchors := (List.range (U.parts.length - parts.length)).map MVertex.anchor
  let (verts, edges) := assemble P parts g clauses
  let n := varCount clauses
  commonK P <| (List.range (2 ^ n)).map fun env =>
    (formulaSat env clauses,
     { verts, edges, anchors,
       selected := (List.range n).map fun v =>
         if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v,
       forbidden := (List.range n).map fun v =>
         if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v })

-- -------------------------------------------------------- slice selection

/-- Move one size-3 part of a composition to the declared negative-layer
    position (parts are labels, so one arrangement per composition covers
    the slice). -/
-- [opus5.5 review] latent: `List.insertIdx` past the end returns the list
-- unchanged, so for p ≥ 1 a composition with fewer than p + 1 parts loses
-- its size-3 part (open item M5b, History.md). Every registered problem
-- uses p = 0; left unchanged because the proof layer depends on it.
def arrangeNeg (c : List Nat) (p : Nat) : List Nat :=
  (c.erase 3).insertIdx p 3

/-- The slices a sweep runs at auxiliary budget `k`, and the compositions
    it skips: the requireLayer pre-filter, then -- for a problem with a
    negative-literal layer -- keep exactly the compositions containing a
    size-3 part, arranged with that part at the declared position. One pure
    function consumed by the sweep, the tests, and the audit guard alike. -/
def slicesFor (negLayer : Option Nat) (k : Nat) (sizes : List Nat)
    (symmetry requireLayer : Bool) : List (List Nat) × List (List Nat) :=
  let slices :=
    if symmetry then
      (compositions k sizes).filter fun (c : List Nat) =>
        !requireLayer || c.any fun s => s == 3 || s == 6
    else
      [List.replicate k 1]
  match negLayer with
  | some p =>
    let (ok, bad) := slices.partition fun (c : List Nat) => c.contains 3
    (ok.map (arrangeNeg · p), bad)
  | none => (slices, [])

end Atlas
