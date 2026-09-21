/-!
  The 3-coloring check.

  Vertices are numbers: the literals x0 x1 x2 are 0 1 2, the palette anchors
  G_T G_F G_B are 3 4 5, and the auxiliary vertices start at 6. A graph is an
  array of adjacency bitmasks.
-/

abbrev Graph := Array Nat

def addEdges (g : Graph) (es : List (Nat × Nat)) : Graph :=
  es.foldl (fun g (u, v) => (g.modify u (· ||| 1 <<< v)).modify v (· ||| 1 <<< u)) g

/-- The edges of every gadget: the palette triangle and x_i -- G_B. -/
def baseGraph (n : Nat) : Graph :=
  addEdges (Array.replicate n 0) [(3, 4), (4, 5), (3, 5), (0, 5), (1, 5), (2, 5)]

/-- Is there a proper 3-coloring with G_T, G_F, G_B colored T, F, B and the
    literals colored by `input` (bit i set: x_i = T, else F)? Backtracking in
    vertex order; cT, cF, cB are the sets of vertices colored so far. -/
partial def accepts (g : Graph) (input : Nat) : Bool :=
  let rec go (v cT cF cB : Nat) : Bool :=
    if v == g.size then true else
    -- the color a literal or an anchor must take: 0 = T, 1 = F, 2 = B; 3 = any
    let pin := if v < 3 then 1 - (input >>> v &&& 1) else if v < 6 then v - 3 else 3
    let ok := fun c used => (pin == 3 || pin == c) && g[v]! &&& used == 0
    (ok 0 cT && go (v + 1) (cT ||| 1 <<< v) cF cB) ||
    (ok 1 cF && go (v + 1) cT (cF ||| 1 <<< v) cB) ||
    (ok 2 cB && go (v + 1) cT cF (cB ||| 1 <<< v))
  go 0 0 0 0

/-- The satisfiable inputs are still colorable. A symmetric graph has four
    input classes: FFF, TFF, TTF, TTT. -/
def alive (g : Graph) : Bool := [1, 3, 7].all (accepts g)

/-- A symmetric gadget is valid if it accepts exactly the satisfiable classes. -/
def valid (g : Graph) : Bool := alive g && !accepts g 0

/-- Validity of any gadget, against all eight inputs. -/
def validAll (g : Graph) : Bool := (List.range 8).all fun i => accepts g i == (i != 0)
