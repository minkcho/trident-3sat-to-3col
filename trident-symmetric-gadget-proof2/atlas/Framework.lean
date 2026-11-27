import atlas.Atlas
/-!
  framework : the generic verification pipeline over the atlas engine.

  A `Problem` packages what one target problem must know: its framework
  (anchor parts, forced edges) and its constraint verifier, which judges a
  graph under one input. Everything else is generic and lives here: the four
  gadget input classes, the budget read off the table (threshold separation),
  the faithful column, the gadget check `gadgetK`, and the pruned search
  `searchSlice`. This package keeps only the parts that 3-coloring and the
  proof of Theorem 16 use.
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

/-- Vertices of a multi-clause graph. Only the type of `Problem.layer` uses it
    here; the multi-clause check is not part of this package. -/
inductive MVertex
  | pos (v : Nat)             -- literal-layer vertex x_v
  | neg (v : Nat)             -- literal-layer vertex ~x_v
  | anchor (p : Nat)          -- shared anchor (attach-appended part p)
  | aux (c p j : Nat)         -- clause c's copy of auxiliary vertex (p, j)
deriving Repr, DecidableEq, Inhabited

abbrev MEdge := MVertex × MVertex

/-- A target problem: its framework and its constraint verifier.

    `measure` is the problem's objective κ under an input (the target column);
    `exact` asks whether the budget k is realized in agreement with the input
    (the faithful column); `target` is the threshold form relating the budget
    to a row's objective. `negLayer` names the auxiliary layer realizing the
    negative literals, when the gadget carries one; `layer` is the
    per-variable literal-layer gadget (not used in this package). -/
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
    that the class collapse relies on. 3-coloring has no negative layer. -/
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

end Atlas
