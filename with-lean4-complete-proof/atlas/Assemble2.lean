import atlas.Framework
/-!
  The generalized assembler, as dictated by the taxonomy
  (`assembler-taxonomy.md`; [opus5.5 review] not in this project -- copies
  are in 3SAT-GRAPH/current/): every sound uniform assembly is

      quotient (merge) of the occurrence-level carrier  +  wiring.

  The occurrence carrier is formula-content-independent: `occMapVertex`
  places literal ports on occurrence vertices `occ c i` (and negative
  ports on their co-ports) without looking at the clause's literals; the
  formula enters only through `merge` (which vertex classes are
  identified), `wiring` (the consistency/decoration edges) and the pins.

  Instances:
  * Phase 1  = `merge = mergeByLiteral` + the problem's layer as wiring --
    `phase1Assemble` reproduces `assemble` verbatim (asserted in tests,
    proved here as `phase1Assemble_eq_assemble`, ProofsAssemble2.lean --
    [opus5.5 review] reference updated);
  * Phase 2  = `merge = id` + a per-problem occurrence wiring (the
    CLIQUE / IS wirings of the full line; not needed for 3-coloring, only
    the carrier `occAssemble` that the interface theorems are stated on).
-/

namespace Atlas

/-- The occurrence-level vertex carrier. -/
inductive OVertex
  | occ (c i : Nat)      -- clause c's i-th literal occurrence
  | occNeg (c i : Nat)   -- its negative co-port (negLayer, occurrence level)
  | anchor (p : Nat)     -- shared anchor (attach-appended part p)
  | aux (c p j : Nat)    -- clause c's copy of auxiliary vertex (p, j)
deriving Repr, DecidableEq, Inhabited

abbrev OEdge := OVertex × OVertex

def OVertex.enc : OVertex → Nat
  | .occ c i => (c * 100 + i) * 2
  | .occNeg c i => (c * 100 + i) * 2 + 1
  | .anchor p => 100000 + p
  | .aux c p j => 200000 + (c * 100 + p) * 100 + j

def normO (e : OEdge) : OEdge :=
  if e.1.enc ≤ e.2.enc then e else (e.2, e.1)

/-- Place one gadget vertex of clause `c` on the occurrence carrier. Note
    the absence of the clause's literal content -- only merge/wiring/pins
    see the formula. -/
def occMapVertex (P : Problem) (own c : Nat) : Vertex → OVertex
  | .lit i => .occ c i
  | .aux p j =>
    if p ≥ own then .anchor (p - own)
    else if P.negLayer == some p then .occNeg c j
    else .aux c p j

/-- The general assembler: gadget copies on the occurrence carrier, pushed
    through `merge` into the target vertex space, unioned with `wiring`. -/
def assembleVia {V : Type} [BEq V] (normV : V × V → V × V)
    (merge : OVertex → V) (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) (wiring : List (V × V)) (baseVerts : List V) :
    List V × List (V × V) :=
  let own := parts.length
  let copies := (List.range clauses.length).flatMap fun c =>
    g.map fun e => normV (merge (occMapVertex P own c e.1),
                          merge (occMapVertex P own c e.2))
  let edges := (copies ++ wiring.map normV).eraseDups.filter fun e => e.1 != e.2
  ((baseVerts ++ edges.flatMap fun e => [e.1, e.2]).eraseDups, edges)

-- ------------------------------------------- row 1: Phase 1 as a quotient

/-- The by-literal quotient: occurrences of the same literal collapse onto
    the shared layer vertex, co-ports onto the opposite polarity. -/
def mergeByLiteral (clauses : List ClauseSpec) : OVertex → MVertex
  | .occ c i => litVertex ((clauses.getD c []).getD i (0, true))
  | .occNeg c i => negLitVertex ((clauses.getD c []).getD i (0, true))
  | .anchor p => .anchor p
  | .aux c p j => .aux c p j

/-- Phase 1 = the general assembler at the by-literal quotient with the
    problem's literal-layer gadget as wiring. Reproduces `assemble`. -/
def phase1Assemble (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) : List MVertex × List MEdge :=
  let n := varCount clauses
  assembleVia normM (mergeByLiteral clauses) P parts g clauses (P.layer n)
    ((List.range n).flatMap fun v => [MVertex.pos v, MVertex.neg v])

-- ------------------------------------------ row 2: Phase 2 (no quotient)

/-- All occurrence vertices of the formula. -/
def occVerts (clauses : List ClauseSpec) : List OVertex :=
  ((List.range clauses.length).zip clauses).flatMap fun (c, clause) =>
    (List.range clause.length).map fun i => OVertex.occ c i

/-- Phase 2 = the general assembler with no quotient and a per-problem
    occurrence wiring. -/
def occAssemble (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec) (wiring : List OEdge) :
    List OVertex × List OEdge :=
  assembleVia normO id P parts g clauses wiring (occVerts clauses)

/-- Does assignment `env` satisfy the literal? -/
def litSat (env : Nat) (l : Nat × Bool) : Bool :=
  (env >>> l.1 &&& 1 == 1) == l.2

/-- Number of satisfied clauses -- the semantic quantity the exclusion-type
    wirings realize as max clique / max independent set. -/
def satCount (clauses : List ClauseSpec) (env : Nat) : Nat :=
  clauses.countP fun c => c.any (litSat env)

end Atlas
