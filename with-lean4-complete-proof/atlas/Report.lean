import atlas.Framework
/-!
  report : LaTeX reports for found gadgets (the atlas counterpart of
  new/NPReduction/Engine/CandidateReport.lean, rendered as a standalone
  compilable document instead of markdown).

  A report contains the summary, an automatically laid-out TikZ figure of the
  gadget (literals on the bottom row, each auxiliary part on its own row,
  anchors on the left, in the style of the paper's figures), the on/off state
  of every edge orbit, the gadget truth-assignment table, and the faithful
  multi-clause table on the two-clause micro-universe.
-/

namespace Atlas

-- ------------------------------------------------------------ vertex naming

def texName (own : Nat) (anchorNames : List String) : Vertex → String
  | .lit i => s!"x_{i}"
  | .aux p j =>
    if p ≥ own then anchorNames.getD (p - own) s!"A_{p - own}"
    else s!"{("pqrstuvw".toList.getD p 'a').toString}_{j}"

def texId : Vertex → String
  | .lit i => s!"x{i}"
  | .aux p j => s!"a{p}v{j}"

-- ------------------------------------------------------------- tikz layout

private def tenths (n : Nat) : String :=
  s!"{n / 10}.{n % 10}"

/-- Literals on the bottom row, own part p on row p+1, anchors on the left. -/
def texCoord (own : Nat) (U : Universe) : Vertex → String
  | .lit i => s!"({tenths (i * 20)},0)"
  | .aux p j =>
    if p ≥ own then
      s!"(-2.8,{tenths (10 + (p - own) * 20)})"
    else
      let s := U.size p
      let x := if s == 1 then 20 else j * 40 / (s - 1)
      s!"({tenths x},{tenths ((p + 1) * 20)})"

def tikzFigure (own : Nat) (U : Universe) (anchorNames : List String)
    (g : List Edge) : String :=
  let node := fun (v : Vertex) =>
    let style := match v with
      | .lit _ => "lit"
      | .aux p _ => if p ≥ own then "anc" else "aux"
    s!"  \\node[{style}] ({texId v}) at {texCoord own U v} \{${texName own anchorNames v}$};"
  let used := (g.flatMap fun e => [e.1, e.2]).eraseDups
  let verts := U.vertices.filter fun v =>
    used.contains v || (match v with | .lit _ => true | _ => false)
  let edges := g.map fun e => s!"  \\draw[thick] ({texId e.1}) -- ({texId e.2});"
  String.intercalate "\n" <|
    ["\\begin{tikzpicture}[scale=0.9,",
     "  lit/.style={circle, draw, thick, minimum size=0.8cm, inner sep=0pt},",
     "  aux/.style={circle, draw, thick, fill=gray!15, minimum size=0.8cm, inner sep=0pt},",
     "  anc/.style={circle, draw, thick, fill=green!10, minimum size=0.8cm, inner sep=0pt}]"] ++
    verts.map node ++ edges ++ ["\\end{tikzpicture}"]

-- ------------------------------------------------------------------ tables

private def passFail (b : Bool) : String := if b then "pass" else "fail"

private def envBits (n env : Nat) : String :=
  String.ofList <| (List.range n).map fun i =>
    if env >>> i &&& 1 == 1 then 'T' else 'F'

private def renderKappa : Option Nat → String
  | some a => toString a
  | none => "--"

private def rowLine (P : Problem) {α : Type} [BEq α]
    (n env : Nat) (isSat : Bool) (inst : Instance α) (k : Nat) : String :=
  let kappa := P.measure inst
  let target := match kappa with
    | some a => P.target isSat k a
    | none => false
  let satText := if isSat then "sat" else "unsat"
  s!"{envBits n env} & {satText} & {renderKappa kappa} & {passFail target} \
& {passFail (P.exact inst k == isSat)} \\\\"

def gadgetTableTex (P : Problem) (parts : List Nat) (g : List Edge)
    (k : Nat) (symmetry : Bool) : String :=
  let (U, _) := P.attach parts
  let anchors := anchorsOf parts.length U
  let rows := (gadgetEnvs symmetry).map fun env =>
    let (sel, forb) := envSidesGadget P env
    rowLine P 3 env (env != 0)
      { verts := U.vertices, edges := g, anchors, selected := sel, forbidden := forb } k
  String.intercalate "\n" <|
    ["\\begin{tabular}{lllll}", "\\toprule",
     "env & clause & $\\kappa$ & target & faithful \\\\", "\\midrule"] ++
    rows ++ ["\\bottomrule", "\\end{tabular}"]

def multiTableTex (P : Problem) (parts : List Nat) (g : List Edge)
    (clauses : List ClauseSpec := microUniverse) : String :=
  let (U, _) := P.attach parts
  let anchors := (List.range (U.parts.length - parts.length)).map MVertex.anchor
  let (verts, edges) := assemble P parts g clauses
  let n := varCount clauses
  let kText := match multiK P parts g clauses with
    | some k => s!"passed with $k = {k}$"
    | none => "failed"
  -- [opus5.5 review] on a failed micro-universe (`none`) the columns below
  -- are judged against k = 0, which fails every row and hides the row that
  -- actually broke (every independent-set and clique find). Left unchanged:
  -- the committed atlas/reports were generated this way and were reproduced
  -- byte for byte on 2026-09-23. Suggested: call `multiK` once and, on
  -- `none`, use the κ of the first satisfiable row.
  let k := (multiK P parts g clauses).getD 0
  let rows := (List.range (2 ^ n)).map fun env =>
    let inst : Instance MVertex :=
      { verts, edges, anchors,
        selected := (List.range n).map fun v =>
          if env >>> v &&& 1 == 1 then MVertex.pos v else .neg v,
        forbidden := (List.range n).map fun v =>
          if env >>> v &&& 1 == 1 then MVertex.neg v else .pos v }
    rowLine P n env (formulaSat env clauses) inst k
  String.intercalate "\n" <|
    [s!"Micro-universe check: {kText}.", "\\medskip", "",
     "\\begin{tabular}{lllll}", "\\toprule",
     "env & formula & $\\kappa$ & target & faithful \\\\", "\\midrule"] ++
    rows ++ ["\\bottomrule", "\\end{tabular}"]

-- -------------------------------------------------------------- the report

def switchesTex (own : Nat) (U : Universe) (anchorNames : List String)
    (g : List Edge) (symmetry : Bool) : String :=
  let label := fun (e : Edge) =>
    s!"${texName own anchorNames e.1}$--${texName own anchorNames e.2}$"
  if symmetry then
    let lines := U.orbits.map fun orbit =>
      let state := if orbit.all g.contains then "on" else "off"
      s!"\\item[{state}] {String.intercalate ", " (orbit.map label)}"
    String.intercalate "\n" <|
      ["\\begin{description}"] ++ lines ++ ["\\end{description}"]
  else
    String.intercalate ", " (g.map label)

def latexReport (P : Problem) (parts : List Nat) (g : List Edge) (k : Nat)
    (symmetry : Bool := true) (anchorNames : List String := []) : String :=
  let (U, _) := P.attach parts
  let own := parts.length
  s!"\\documentclass[11pt]\{article}
\\usepackage\{tikz}
\\usepackage\{booktabs}
\\usepackage[margin=1in]\{geometry}
\\begin\{document}

\\section*\{{P.name} clause gadget}

\\begin\{itemize}
\\item composition: parts = {toString parts} (aux vertices: {parts.foldl (· + ·) 0}, \
$N = {U.vertices.length}$, edges: {g.length})
\\item derived budget: $k = {k}$
\\item row regime: {if symmetry then "four symmetry classes" else "all eight assignments"}
\\end\{itemize}

\\subsection*\{The gadget}

\\begin\{center}
{tikzFigure own U anchorNames g}
\\end\{center}

\\subsection*\{Edge orbits}

{switchesTex own U anchorNames g symmetry}

\\subsection*\{Truth-assignment table}

{gadgetTableTex P parts g k symmetry}

\\subsection*\{Multi-clause check ($C_1 = x_0 \\lor x_1 \\lor x_2$, \
$C_2 = \\lnot x_0 \\lor x_1 \\lor x_3$)}

{multiTableTex P parts g}

\\end\{document}
"

def writeReport (dir stem : String) (P : Problem) (parts : List Nat)
    (g : List Edge) (k : Nat) (symmetry : Bool := true)
    (anchorNames : List String := []) : IO String := do
  IO.FS.createDirAll dir
  let path := s!"{dir}/{stem}.tex"
  IO.FS.writeFile path (latexReport P parts g k symmetry anchorNames)
  pure path

end Atlas
