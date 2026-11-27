import search.Statement
import proof.Definition2
import proof.ClauseGadget

/-!
  Dependency check: which declarations of the package do its results use?

  The roots are the results of the package. In `proof/`: the two theorems of
  `Theorem16.lean`, the remark after Theorem 16 (`Uniqueness.lean`), and the
  statements of the paper that the theorems do not use as stated (Lemma 6 as
  one statement, Claim 1 on fibers, Lemma 11 for arbitrary clause gadgets).
  In `search/`: the statements of `Statement.lean` and of `Space.lean`. The
  check follows types, definition bodies and proofs from the roots (core
  Lean and Mathlib are library and are not followed) and prints every
  declaration of the package that is never reached. Auxiliary constants
  (`match_1`, `proof_1`, `eq_1`, private names) count as the declaration that
  owns them, and the declarations Lean generates for structures, inductive
  types and `deriving` clauses are listed separately.

  Run in the built package:   lake env lean checks/ProofCone.lean
-/

open Lean Elab Command

namespace ProofCone

/-- `pre` followed by numbers, such as `match_1`, `match_1_1` or `eq_2` -/
def numbered (pre s : String) : Bool :=
  s.startsWith pre &&
    match s.toList.drop pre.length with
    | [] => false
    | c :: cs => c.isDigit && cs.all fun d => d.isDigit || d == '_'

/-- A name component that Lean gives to an auxiliary constant. A lemma
    written in the source with a name such as `eq_two_of_ne` is not one. -/
def internalComp (s : String) : Bool :=
  s.startsWith "_" || numbered "match_" s || numbered "proof_" s ||
  numbered "eq_" s || numbered "spec_" s || s == "eq_def" || s == "eq_unfold" ||
  s.startsWith "fun_cases"

/-- the user-facing declaration that owns a (possibly auxiliary) constant -/
def owner (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  let n := n.eraseMacroScopes
  let rec build (acc : Name) : List Name → Name
    | [] => acc
    | c :: cs =>
      match c with
      | .str _ s => if internalComp s then acc else build (.str acc s) cs
      | _ => acc
  build .anonymous n.components

/-- declared in a module of this package (`proof.*` or `search.*`) -/
def inPackage (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`proof).isPrefixOf env.header.moduleNames[idx.toNat]! ||
      (`search).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

/-- the owner of a package constant, when the owner is a declaration of the
    package (an auxiliary constant that Lean names after a core declaration
    is not counted) -/
def pkgOwner? (env : Environment) (n : Name) : Option Name :=
  if inPackage env n then
    let o := owner n
    if !env.contains o || inPackage env o then some o else none
  else none

/-- declarations Lean generates (recursors, no-confusion, injectivity,
    constructors, structure projections, derived instances) -/
def generated (env : Environment) (n : Name) : Bool :=
  let gen := ["casesOn", "recOn", "rec", "brecOn", "below", "binductionOn", "ibelow",
    "noConfusion", "noConfusionType", "ctorIdx", "inj", "injEq", "sizeOf_spec",
    "congr_simp", "ctorElim", "ctorElimType", "elim", "repr", "beq", "default", "decEq",
    "proxyType", "proxyTypeEquiv"]
  (match n with
   | .str _ s => gen.contains s || s.startsWith "instRepr" || s.startsWith "instBEq" ||
       s.startsWith "instInhabited" || s.startsWith "instDecidableEq"
   | _ => false) ||
  (match env.find? n with
   | some (.ctorInfo _) | some (.recInfo _) => true
   | _ => false) ||
  env.isProjectionFn n

def depsOf (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .thmInfo v => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | _ => t

end ProofCone

open ProofCone in
run_cmd do
  let env ← getEnv
  let roots : Array Name :=
    #[``Def1.minimum_unique,
      ``Def1.trident_is_valid_gadget,
      ``Def1.Gadget.lemma6,
      ``Def1.Gadget.fiber_card,
      ``Def1.ClauseGadget.lemma11,
      ``Def1.Gadget.toClauseGadget_spec,
      ``Def1.trident_rigid,
      ``Def1.iso_trident_unique,
      ``Def1.iso_trident_equivariant,
      ``Def1.iso_of_literal_set,
      ``Def1.gadget_is_candidate,
      ``Def1.candidate_is_gadget,
      ``Def1.search_finds_every_valid_gadget,
      ``Atlas.Statement.compositions_are_all_orbit_compositions,
      ``Atlas.Statement.gadgetK_is_validity,
      ``Atlas.Statement.trident_is_symmetric_candidate,
      ``Atlas.Statement.trident_is_valid,
      ``Atlas.Statement.no_valid_symmetric_gadget_below_six_auxiliary_vertices,
      ``Atlas.Statement.valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident,
      ``Atlas.Statement.search_finds_every_valid_candidate,
      ``Atlas.Statement.search_finds_only_valid_candidates,
      ``Atlas.Statement.search_finds_nothing_below_six,
      ``Atlas.Statement.search_finds_only_the_trident,
      ``Atlas.Statement.search_finds_the_trident,
      ``Atlas.Statement.search_finds_nothing_at_six_outside_trident_slice,
      ``Atlas.sym_empty_13,
      ``Atlas.sym_empty_23,
      ``Atlas.sym_empty_113,
      ``Atlas.sym_empty_6,
      ``Atlas.sym_empty_123,
      ``Atlas.sym_empty_1113]
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    for d in depsOf ci do
      if inPackage env d && !seen.contains d then todo := todo.push d
  let used : NameSet := seen.toList.foldl (fun s n => match pkgOwner? env n with | some o => s.insert o | none => s) {}
  let mut owners : NameSet := {}
  for (n, _) in env.constants.toList do
    if let some o := pkgOwner? env n then owners := owners.insert o
  let mut unused : Array Name := #[]
  let mut unusedGen : Array Name := #[]
  for o in owners.toList do
    unless used.contains o do
      if generated env o then unusedGen := unusedGen.push o else unused := unused.push o
  let lt := fun (a b : Name) => decide (a.toString < b.toString)
  IO.println s!"declarations of the package: {owners.size}; used by the results: {used.size}"
  IO.println s!"not used, written in the source: {unused.size}"
  for n in unused.qsort lt do IO.println s!"  {n}"
  IO.println s!"not used, generated by Lean: {unusedGen.size}"
  for n in unusedGen.qsort lt do IO.println s!"  {n}"
