import Color
/-!
  The loop: every S3-symmetric candidate gadget, composition by composition.

      lake exe sweep --max=6          compositions with a size-3 or free orbit
      lake exe sweep --max=6 --all    every orbit composition
      lake exe sweep --test           the numbers and gadgets quoted in the paper

  The k auxiliary vertices form S3-orbits of size 1, 2, 3 or 6 (Lemma 6); the
  list of sizes is an orbit composition, e.g. [3, 3] for the trident. Every
  pair with an auxiliary endpoint is free, binom(k,2) + 6k pairs in all, and
  pairs in the same orbit are present or absent together: a candidate is one
  Boolean choice per edge orbit (a "switch").
-/

-- the group S3 --------------------------------------------------------------

abbrev Perm := Nat × Nat × Nat

def perms : List Perm := [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]

def app (s : Perm) : Nat → Nat
  | 0 => s.1
  | 1 => s.2.1
  | _ => s.2.2

def compose (s t : Perm) : Perm := (app s t.1, app s t.2.1, app s t.2.2)

def odd (s : Perm) : Nat := if [((0,1,2) : Perm), (1,2,0), (2,0,1)].contains s then 0 else 1

/-- The image of vertex v: literals are permuted, anchors are fixed, and an
    auxiliary orbit carries the action of its size (fixed, sign, natural, free). -/
def act (parts : List Nat) (s : Perm) (v : Nat) : Nat :=
  if v < 3 then app s v else if v < 6 then v else
  let rec go (base : Nat) : List Nat → Nat
    | [] => v
    | size :: rest =>
      if v < base + size then
        let j := v - base
        base + match size with
          | 1 => j
          | 2 => j ^^^ odd s
          | 3 => app s j
          | _ => (perms.findIdx? (· == compose s (perms.getD j (0,1,2)))).getD 0
      else go (base + size) rest
  go 6 parts

/-- The switches: the orbits of the free pairs under the action. -/
def switches (parts : List Nat) : List (List (Nat × Nat)) :=
  let pairs := (List.range (6 + parts.sum)).flatMap fun v =>
    if v < 6 then [] else (List.range v).map (·, v)
  pairs.foldl (fun orbits (u, v) =>
    if orbits.any (·.contains (u, v)) then orbits else
    orbits ++ [(perms.map fun s =>
      let (a, b) := (act parts s u, act parts s v)
      (min a b, max a b)).eraseDups]) []

/-- The multisets of orbit sizes that sum to k (one row of Fig. 5). -/
partial def compositions (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) : List (List Nat) :=
  if k == 0 then [[]] else
  match sizes with
  | [] => []
  | s :: rest =>
    (if s ≤ k then (compositions (k - s) sizes).map (s :: ·) else []) ++ compositions k rest

-- the search ----------------------------------------------------------------

structure Stats where
  leaves : Nat := 0
  pruned : Nat := 0
  found : List Graph := []

/-- Decide the switches one by one. Adding edges can only destroy
    3-colorability, so a subtree is pruned as soon as a satisfiable input is
    no longer colorable; leaves + pruned = 2^switches. -/
partial def walk (sw : Array (List (Nat × Nat))) (i : Nat) (g : Graph) (st : Stats) : Stats :=
  if i == sw.size then
    { st with leaves := st.leaves + 1, found := if valid g then g :: st.found else st.found }
  else
    let on := addEdges g sw[i]!
    let st := if alive on then walk sw (i + 1) on st
      else { st with pruned := st.pruned + 2 ^ (sw.size - i - 1) }
    walk sw (i + 1) g st

/-- Exhaust one composition. The settings of the first d switches that are
    still alive are dealt out to 16 threads in turn; the result does not
    depend on the number of cores. -/
def search (parts : List Nat) : Stats :=
  let sw := (switches parts).toArray
  let d := min 10 sw.size
  let start := fun (p : Nat) => (List.range d).foldl (fun g i =>
    if p >>> i &&& 1 == 1 then addEdges g sw[i]! else g) (baseGraph (6 + parts.sum))
  let (live, dead) := (List.range (2 ^ d)).partition fun p => alive (start p)
  let tasks := (List.range 16).map fun w => Task.spawn (prio := .dedicated) fun _ =>
    ((List.range live.length).filter (· % 16 == w)).foldl (fun st j =>
      walk sw d (start live[j]!) st) {}
  tasks.foldl (fun a t => let b := t.get
    { leaves := a.leaves + b.leaves, pruned := a.pruned + b.pruned, found := a.found ++ b.found })
    { pruned := dead.length * 2 ^ (sw.size - d) }

-- the gadgets of the paper --------------------------------------------------

/-- Fig. 2(c): branches p_i = p + i, upper triangle u_i = u + i. -/
def trident (p u : Nat) : Graph :=
  addEdges (baseGraph 12) <| (List.range 3).flatMap fun i =>
    [(i, p + i), (3, p + i), (p + i, u + i), (u + i, u + (i + 1) % 3)]

/-- Fig. 2(a): the trident with the upper triangle replaced by a path whose
    ends are tied to G_T and G_F. -/
def kleinbergTardos : Graph :=
  addEdges (baseGraph 12) [(0, 6), (1, 7), (2, 8), (3, 6), (3, 7), (3, 8),
    (6, 9), (7, 10), (8, 11), (9, 10), (10, 11), (3, 9), (4, 11)]

/-- Fig. 2(b): a triangle attached to the literals (the NAE-3SAT gadget). -/
def sharmaChaudhari : Graph :=
  addEdges (baseGraph 9) [(0, 6), (1, 7), (2, 8), (6, 7), (7, 8), (6, 8)]

/-- Fig. 1(c): two chained OR gadgets. -/
def orChain : Graph :=
  addEdges (baseGraph 11) [(0, 6), (1, 7), (6, 7), (6, 8), (7, 8), (8, 9),
    (2, 10), (9, 10), (9, 3), (10, 3)]

def vertexName (v : Nat) : String := (["x0", "x1", "x2", "GT", "GF", "GB"][v]?).getD s!"{v}"

/-- The edges of a gadget other than the fixed ones. -/
def showEdges (g : Graph) : String :=
  let base := baseGraph g.size
  " ".intercalate <| (List.range g.size).flatMap fun v => (List.range v).filterMap fun u =>
    if g[u]! >>> v &&& 1 == 1 && base[u]! >>> v &&& 1 == 0
    then some s!"{vertexName u}-{vertexName v}" else none

-- main ----------------------------------------------------------------------

def check (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"ok  {name}" else throw (IO.userError s!"FAILED  {name}")

def test : IO Unit := do
  for k in [4, 5, 6, 7] do
    let free := k * (k - 1) / 2 + 6 * k
    check s!"N={k + 6}: binom(k,2)+6k = {free} free pairs" <|
      (compositions k).all fun p => ((switches p).map List.length).sum == free
    check s!"N={k + 6}: k fixed vertices have binom(k,2)+4k = {free - 2 * k} switches" <|
      (switches (List.replicate k 1)).length == free - 2 * k
    let total := ((compositions k).map fun p => 2 ^ (switches p).length).sum
    IO.println s!"    N={k + 6}: unconstrained 2^{free}, S3-symmetric {total} (about 2^{total.log2})"
  check "two size-3 orbits: 2^14 candidates" ((switches [3, 3]).length == 14)
  check "trident (Fig. 2(c)) is valid" (validAll (trident 6 9))
  check "Kleinberg-Tardos (Fig. 2(a)) is valid" (validAll kleinbergTardos)
  check "OR-chain (Fig. 1(c)) is valid" (validAll orChain)
  check "Sharma-Chaudhari (Fig. 2(b)) rejects (T,T,T)" (!accepts sharmaChaudhari 7)

def main (args : List String) : IO Unit := do
  if args.contains "--test" then test else
  let all := args.contains "--all"
  let maxK := ((args.find? (·.startsWith "--max=")).bind fun a => (a.drop 6).toNat?).getD 6
  let mut valids := 0
  for k in List.range (maxK + 1) do
    -- fewest switches first: the compositions with the largest orbits
    let comps := ((compositions k).filter fun p => all || p.any (· ≥ 3)).toArray.qsort
      fun p q => (switches p).length < (switches q).length
    for parts in comps do
      let sw := switches parts
      let t0 ← IO.monoMsNow
      let st ← IO.lazyPure fun _ => search parts
      let t1 ← IO.monoMsNow
      IO.println s!"N={k + 6} {parts}: K={(sw.filter fun o => o.all fun e => e.1 < 3 || e.1 ≥ 6).length} \
switches={sw.length} candidates=2^{sw.length} leaves={st.leaves} pruned={st.pruned} \
valid={st.found.length} ({t1 - t0} ms)"
      if st.leaves + st.pruned != 2 ^ sw.length then
        throw (IO.userError "leaves + pruned != candidates")
      for g in st.found do
        IO.println s!"  valid: {showEdges g}"
        IO.println s!"  is the trident: {g == trident 6 9 || g == trident 9 6}"
      valids := valids + st.found.length
  IO.println s!"{valids} valid gadget(s) with N <= {maxK + 6}"
