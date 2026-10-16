/-!
  atlas : a tiny S3-symmetric gadget-graph generator.

  A clause of 3SAT is invariant under the six permutations of its three
  literals, so a clause gadget worth searching for should be too. This module
  generates candidate graphs over three literal vertices plus auxiliary
  vertices organized into S3-orbits ("parts") of size 1, 2, 3 or 6 -- the only
  sizes an S3-orbit can have (orbit-stabilizer):

      size 1  a fixed vertex (an anchor, or a general auxiliary vertex)
      size 2  a twin pair carrying the sign action (odd permutations swap it)
      size 3  a layer carrying the natural action
      size 6  a free orbit (a regular copy of S3 itself)

  Because a single edge drags its whole orbit along, an S3-symmetric graph is
  determined by a subset of *edge orbits*, and the generator just walks those
  subsets. Turning symmetry off means each raw edge becomes its own switch --
  same universe, same walk, exponentially more of it.

  The per-composition switch counts reproduce, composition by composition, the
  "S3 orbit space" column of the search-space table in the trident paper
  (sum over `atlas k` of 2^K: 1,248 / 35,648 / 2,179,968 / 273,101,312 for
  k = 4..7). See Tests.lean and Demo.lean.
-/

namespace Atlas

-- ----------------------------------------------------------------- the group

/-- A permutation of {0,1,2} as its value table (s 0, s 1, s 2). -/
abbrev Perm := Nat × Nat × Nat

def perms : List Perm := [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]

def app (s : Perm) : Nat → Nat
  | 0 => s.1
  | 1 => s.2.1
  | _ => s.2.2

/-- (compose s t) i = s (t i) -- apply t first, then s. -/
def compose (s t : Perm) : Perm := (app s t.1, app s t.2.1, app s t.2.2)

def parity (s : Perm) : Nat :=
  if [((0,1,2) : Perm), (1,2,0), (2,0,1)].contains s then 0 else 1

def pidx (s : Perm) : Nat := (perms.findIdx? (· == s)).getD 0

-- -------------------------------------------------------------- the universe

inductive Vertex
  | lit (i : Nat)
  | aux (part j : Nat)
deriving Repr, BEq, Inhabited

abbrev Edge := Vertex × Vertex

/-- A total order key so every edge has one normal form. -/
def Vertex.key : Vertex → Nat
  | .lit i => i
  | .aux p j => 3 + 6 * p + j

def normEdge (e : Edge) : Edge :=
  if e.1.key ≤ e.2.key then e else (e.2, e.1)

def unorderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

/-- Three literal vertices plus auxiliary parts of sizes 1, 2, 3 or 6.
    Literal-literal edges are excluded unless `litLit` is set (the literals of
    a clause gadget are pairwise non-adjacent). -/
structure Universe where
  parts : List Nat
  litLit : Bool := false
deriving Repr

namespace Universe

def size (U : Universe) (p : Nat) : Nat := U.parts.getD p 0

def vertices (U : Universe) : List Vertex :=
  (List.range 3).map .lit ++
    (List.range U.parts.length).flatMap fun p =>
      (List.range (U.size p)).map (Vertex.aux p)

/-- The action of a permutation on a vertex, per orbit type. -/
def act (U : Universe) (s : Perm) : Vertex → Vertex
  | .lit i => .lit (app s i)
  | .aux p j =>
    match U.size p with
    | 1 => .aux p j                                        -- fixed
    | 2 => .aux p (j ^^^ parity s)                         -- sign action
    | 3 => .aux p (app s j)                                -- natural action
    | _ => .aux p (pidx (compose s (perms.getD j (0,1,2)))) -- regular (free)

def edges (U : Universe) : List Edge :=
  (unorderedPairs U.vertices).filterMap fun e =>
    match e with
    | (.lit _, .lit _) => if U.litLit then some (normEdge e) else none
    | _ => some (normEdge e)

def actEdge (U : Universe) (s : Perm) (e : Edge) : Edge :=
  normEdge (U.act s e.1, U.act s e.2)

def edgeOrbit (U : Universe) (e : Edge) : List Edge :=
  (perms.map fun s => U.actEdge s e).eraseDups

/-- Edge orbits under the action: the independent symmetric switches. -/
def orbits (U : Universe) : List (List Edge) :=
  let rec go : List Edge → List Edge → List (List Edge)
    | [], _ => []
    | e :: rest, seen =>
      if seen.contains e then
        go rest seen
      else
        let orb := U.edgeOrbit e
        orb :: go rest (seen ++ orb)
  go U.edges []

/-- The on/off switches: edge orbits, or single edges when symmetry is off. -/
def switches (U : Universe) (symmetry : Bool := true) : List (List Edge) :=
  if symmetry then U.orbits else U.edges.map ([·])

def count (U : Universe) (symmetry : Bool := true) : Nat :=
  2 ^ (U.switches symmetry).length

/-- Split the switches into the forced base (orbits touching a `forced` edge,
    always on) and the freely enumerated rest. -/
def splitForced (U : Universe) (forced : List Edge)
    (symmetry : Bool := true) : List Edge × List (List Edge) :=
  let forced := forced.map normEdge
  let isForced := fun (g : List Edge) => forced.any g.contains
  let sw := U.switches symmetry
  ((sw.filter isForced).flatten, sw.filter (fun g => !isForced g))

end Universe

/-- The candidate graph selected by a bitmask over the free switches. -/
def graphAt (base : List Edge) (free : List (List Edge)) (mask : Nat) : List Edge :=
  base ++ ((List.range free.length).zip free).flatMap fun (i, g) =>
    if mask >>> i &&& 1 == 1 then g else []

/-- Every candidate graph of the universe (use only when 2^K is small). -/
def Universe.graphs (U : Universe) (symmetry : Bool := true)
    (forced : List Edge := []) : List (List Edge) :=
  let (base, free) := U.splitForced forced symmetry
  (List.range (2 ^ free.length)).map (graphAt base free)

-- ------------------------------------------------------------------ the atlas

/-- The legal orbit sizes present in `sizes`, ascending and distinct: walk
    the canon, keep what is present. Total and directly provable (a filter
    of an explicit strictly sorted list), which is why the enumeration
    below is built on it. -/
def legalSizes (sizes : List Nat) : List Nat :=
  [1, 2, 3, 6].filter sizes.contains

/-- Non-decreasing lists over the allowed suffix summing to the budget:
    use the head size again or drop to the tail. Total (the guard carries
    the s >= 1 evidence the termination argument needs), and the recursion
    is what `atlas/Proofs.lean` proves sound, complete and count-exact. -/
def compositionsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, s :: rest =>
    (if h : 1 ≤ s ∧ s ≤ k + 1 then
      (compositionsAux (k + 1 - s) (s :: rest)).map (s :: ·)
     else []) ++ compositionsAux (k + 1) rest
termination_by k ss => k + ss.length
decreasing_by all_goals (simp only [List.length_cons]; omega)

/-- All multisets of part sizes summing to k, e.g. k = 4 over (1,2,3,6) gives
    [1,1,1,1], [1,1,2], [1,3], [2,2]. This is the row of the enumeration
    atlas at k. -/
def compositions (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) : List (List Nat) :=
  compositionsAux k (legalSizes sizes)

/-- One Universe per orbit-type composition of k auxiliary vertices. -/
def atlas (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) (litLit : Bool := false) :
    List Universe :=
  (compositions k sizes).map fun parts => { parts, litLit }

/-- (parts, K, 2^K) per composition; the total is the S3 orbit space at k. -/
def census (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) : List (List Nat × Nat × Nat) :=
  (atlas k sizes).map fun U => (U.parts, U.orbits.length, U.count)

def orbitSpace (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) : Nat :=
  (census k sizes).foldl (fun acc row => acc + row.2.2) 0

end Atlas
