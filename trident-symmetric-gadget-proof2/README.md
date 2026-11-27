# Lean 4 proof, second version: the trident as the minimum S3-symmetric clause gadget

A machine-checked proof, in Lean 4 with Mathlib, of Theorem 16 of the paper:
every valid S3-symmetric clause gadget for the reduction from 3SAT to
3-coloring has at least six auxiliary vertices, and one with six is the
trident. The theorem is stated for the paper's Definition 1 with Mathlib's
graphs and permutations
([`atlas/Definition1.lean`](atlas/Definition1.lean),
[`atlas/Theorem16.lean`](atlas/Theorem16.lean)).

A gadget of Definition 1 has six fixed vertices, the three literals (the
input) and the palette triangle (the fixed colors), and auxiliary vertices.
The result counts the auxiliary vertices added to these six. It is not
about arbitrary graphs with at most twelve vertices.

The proof has two layers. The orbit types of the paper's Lemma 6 (orbit
structure) turn a gadget of Definition 1 into a candidate of a search
engine. In the engine's
candidate space the result follows from two proved reductions and an
exhaustive search whose runs are repeated at build time, seven of them by
compiled code (see "Trusted base").

This folder is the second version of `../trident-symmetric-gadget-proof/`.
The first version proves the result for the candidates of the search engine
and names its statements by the total number of vertices. This version adds
the step from Definition 1 to the candidates, states the theorem for
Definition 1 by the number of auxiliary vertices, and keeps only the
declarations that its statements use. The last section lists the
differences.

The report [`report/proof-report.pdf`](report/proof-report.pdf) explains the
statements, follows the proof, and lists the trusted base and what is not
formalized.

The formal verification was written with Claude (Anthropic) and is under
evaluation by the authors. It is not part of the paper, which proves
Theorem 16 by the argument of its Section IV.

## For reviewers

You do not need to read the proofs, because Lean checks them. What needs
checking is that the statements say what the paper claims.

1. Read [`atlas/Definition1.lean`](atlas/Definition1.lean), 97 lines. It
   uses Mathlib only and no engine code. It defines an S3-symmetric clause
   gadget (`Gadget`), its auxiliary vertices (`Gadget.IsAux`), its validity
   (`Gadget.Extends`, `Gadget.Valid`) and the trident graph (`TV`,
   `tridentEdge`, `trident`).
2. Read the two theorems at the end of
   [`atlas/Theorem16.lean`](atlas/Theorem16.lean):
   - `trident_is_valid_gadget`: the trident is a valid S3-symmetric clause
     gadget with six auxiliary vertices (twelve vertices in total);
   - `minimum_unique`: every valid S3-symmetric clause gadget on a finite
     vertex set has at least six auxiliary vertices, added to its six fixed
     vertices, and one with exactly six is isomorphic to the trident by an
     isomorphism that fixes each literal and each anchor.

   These two statements use only the seven definitions of step 1.
3. Run `lake exe cache get` and then `lake build`. The build checks every
   proof and prints the axioms of the two theorems and of the seven
   statements below. The first build takes about 8 hours 20 minutes (1,380
   jobs, measured on an Intel Core i7-8700), almost all of it in
   `ProofsSweeps16` (six `native_decide` re-runs on one thread); later
   builds reuse the result and take seconds.

### The intermediate statements

[`atlas/Statement.lean`](atlas/Statement.lean), 141 lines, gives seven
statements about the engine's candidate space. Statements 3, 4, 5 and 7 are
steps of the proof of `minimum_unique`; Statements 1, 2 and 6 are not used
by the two theorems. None of the seven is needed to know what is proved. To
check them as well, read the definitions they use: 60 declarations, 349
lines. The table lists 57 of them (314 lines); its ranges also include the
comments between them. The other three are the proofs named below the
table.

| file | lines | what |
|---|---|---|
| `atlas/Atlas.lean` | 32–48, 52–77, 81–108, 150–175 | S3 permutations, vertices, the S3 action, candidate edges, orbit compositions |
| `atlas/Framework.lean` | 16–57, 61–75, 79–130 | instances, the problem interface, the eight-row validity check `gadgetK` |
| `atlas/Kits.lean` | 21–35 | the feasibility kit |
| `atlas/Problems/ThreeColoring.lean` | 16–58 | the 3-coloring check and the palette |
| `atlas/ProofsDecide.lean` | 90–108 | the trident under its two labelings (`tridentA`, `tridentB`) |
| `atlas/Statement.lean` | 37–43 | `SymCandidate` |
| `atlas/ProofsColor.lean` | 28–39 | `SpecExt`: a proper coloring that respects the pins (Statement 7) |
| `atlas/ProofsSym.lean` | 636–640, 816–821 | `rowPins`, `rowInst`: the instance of one input row (Statement 7) |
| `atlas/ProofsColorK.lean` | 23–31 | `colorAt`, `combined`, used by `SpecExt` |
| `atlas/ProofsOrbit.lean` | 29–41, 69–77 | `S3` as a group, `LegalUniverse` (Statement 6) |
| `atlas/ProofsAction.lean` | 92–94, 425–427 | `Universe.legal`, `pinv` (Statement 6) |

Statements 1–4 alone use 41 of these declarations (257 lines), all in the
first six rows. The table leaves out three proofs that these definitions
refer to: `id_mem_perms` (`ProofsAction.lean`, line 35),
`instLawfulBEqVertex` (`ProofsAction.lean`, lines 256–279) and
`attach_legal` (`ProofsSym.lean`, lines 208–217). Lean checks them, and they
do not change what the definitions mean. The same holds for the proofs
inside the `Mul`, `Inv` and `Group` instances of `S3`.

## What is proved

For the paper's Definition 1 (`atlas/Theorem16.lean`):

- `trident_is_valid_gadget`: the trident graph, with its literals and
  anchors, carries an S3-symmetric clause gadget, this gadget is valid (the
  paper's Theorem 4), and it has six auxiliary vertices, the p_i and the
  u_i (twelve vertices in total).
- `minimum_unique`: Theorem 16, as described above.

The orbit types of the paper's Lemma 6, in `atlas/OrbitStructure.lean`
(Mathlib only):

- `orbit_structure`: for a point of a set with an S3 action, the orbit has
  size 1, 2, 3 or 6, and the permutations that fix the point are all of
  them, the even ones, those that fix one index, or the identity only (the
  trivial, sign, natural or free action). The proof is the paper's argument:
  the stabilizer is S3, A3, the stabilizer of an index or trivial, and the
  orbit-stabilizer theorem gives the size of the orbit. In Lean the order of
  the stabilizer comes from Lagrange's theorem.

For the engine's candidate space (`atlas/Statement.lean`):

1. `trident_is_symmetric_candidate`: the trident is an S3-symmetric
   candidate of composition `[3, 3]`.
2. `trident_is_valid`: the trident is a valid clause gadget, on all eight
   inputs.
3. `no_valid_symmetric_gadget_below_six_auxiliary_vertices`: no valid S3-symmetric
   candidate has at most five auxiliary vertices (N ≤ 11).
4. `valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident`: every valid
   S3-symmetric candidate with at most six auxiliary vertices (N ≤ 12) has
   composition `[3, 3]` and is the trident, under one of its two labelings.
5. `compositions_are_all_orbit_compositions`: `compositions k [1, 2, 3, 6]`
   lists exactly the non-decreasing lists over {1, 2, 3, 6} that sum to `k`.
6. `candidate_action_is_s3_action`: for every list of part sizes in
   {1, 2, 3, 6}, `act` satisfies the laws of an action of S3 on the vertices
   (identity, composition, vertices to vertices), permutes the literals
   naturally and fixes the three palette anchors. A Mathlib `MulAction` of
   the group `S3`, the engine's table of six permutations with `compose` as
   multiplication, has `act` as its scalar multiplication. Every edge orbit
   has size 1, 2, 3 or 6.
7. `gadgetK_is_validity`: `gadgetK … false = some b` holds exactly when
   `b = 1` and, for each of the eight inputs, the row is 3-colorable if and
   only if the input satisfies the clause. For a graph inside the candidate
   space, a row is 3-colorable exactly when a proper coloring that respects
   its pins exists.

`minimum_unique` is derived from Statements 3, 4, 5 and 7: the orbit types
of Lemma 6 give every gadget of Definition 1 on a finite vertex set an orbit
composition and a relabeling into the candidate space
(`atlas/Candidate.lean`, `atlas/CandidateGraph.lean`), and a valid gadget
passes the judge `gadgetK` (`gadgetK_of_valid` in
`atlas/CandidateValid.lean`; this package proves this direction only).

### The candidate space and the paper's Table 1

The candidates of an orbit composition are the S3-invariant graphs that
Definition 1 allows on it. The palette triangle and the G_B fan are always
present, literal–literal edges are never present, and every other pair is
switched, one switch per S3 edge orbit. This package proves that every
gadget of Definition 1 on a finite vertex set is such a candidate after a
relabeling of its vertices (`Gadget.symCandidate`, with `Gadget.adj_iff` and
`Gadget.toVertex_injective`). The converse, that every candidate is a gadget
of Definition 1, is `candidate_is_gadget` in
`../paper-proof-and-search-trident_minimum_unique/`. That package also
proves that the relabeling is a bijection (`gadget_is_candidate`).

The paper's enumeration is the program `../Sweep.lean`, and the paper's
Table 1 reports its run. It has two switches fewer for each of the 24
compositions of the table: it leaves out the literal–G_T orbit and the
literal–G_F orbit by the remark after Definition 1. So the engine has four
times as many candidates as Table 1 lists, for example 2^16 for `[3, 3]`,
where the table has 2^14.

## Trusted base

- Lean's kernel and the standard axioms `propext`, `Classical.choice`,
  `Quot.sound`.
- Mathlib v4.33.0.
- The compiler, for seven `native_decide` re-runs of the search: six empty
  sweeps in `ProofsSweeps16.lean` and `trident_slice_found` in
  `ProofsDecide.lean`. Statements 3 and 4 depend on them, and
  `minimum_unique` depends on them through Statements 3 and 4.
  `trident_is_valid_gadget` and Statements 1, 2 and 5–7 do not. The sweep of
  `[3]` is checked by the kernel.

The files for Definition 1 use `decide` (kernel evaluation, standard axioms
only) for checks of concrete data: the engine's hand-written tables of the
six permutations, the encoding of the eight inputs, the comparison of the
edge lists `tridentA` and `tridentB` with the trident graph, the explicit
colorings of the trident and the numbers of its vertices. They also use it
for four small facts about three points or three colors (inside
`exists_fixed_of_sq_eq_one` and `tridentGadget_valid`) and for the
inequality 0 < 3. The report lists them.

## What is not formalized

- The paper's own proof of Theorem 16 (the lemma chain of its Sections IV-A
  to IV-C). The formal proof reaches the statement by the exhaustive search
  in the candidate space. From Section IV it formalizes the orbit types of
  Lemma 6, a special case of Lemma 11, the four-input reduction and, for its
  own engine, that pruning loses no valid candidate.
- The statements of Lemma 6 about the subgraph induced on an orbit of size 3
  and about literal attachments. The proof does not need them.
- The paper's remark after Theorem 16 that the isomorphism onto the trident
  is unique and commutes with the two S3-actions. `minimum_unique` gives the
  existence of the isomorphism only.
- The candidate and leaf counts in the paper's Table 1, which come from the
  enumeration program in the parent folder.
- The other results of the paper.

The first three items are formalized in
`../paper-proof-and-search-trident_minimum_unique/`.

## Dependency check

`checks/ProofCone.lean` follows types, definition bodies and proofs from the
two theorems of `Theorem16.lean` and the seven statements, and lists every
declaration of the package that is never reached. Run it in the built
package:

```
lake env lean checks/ProofCone.lean
```

It reports 635 declarations, 514 used. All 121 unused declarations are
generated by Lean (recursors and the other constants that Lean generates for
each structure and inductive type, derived instances, generated congruence
lemmas, two structure projections). No declaration written in the source is
unused.

## Relation to `paper-proof-and-search-trident_minimum_unique`

The package `../paper-proof-and-search-trident_minimum_unique/` proves the
same two theorems, `minimum_unique` and `trident_is_valid_gadget`, for the
same `Definition1.lean`. It follows the paper's own argument, the lemma
chain of Section IV, and uses no search and no compiled code. It also
contains this search engine and proves, from Theorem 16, the six statements
`sym_empty_…` that this package evaluates by compiled code.

So the two packages reach Theorem 16 in two ways. Here the search proves the
theorem, and the trusted base includes the compiler. There the paper's
argument proves it, and the trusted base is Lean's kernel with the standard
axioms.

## Differences from the first version

The first version is `../trident-symmetric-gadget-proof/`.

- Added: the layer for Definition 1, eight files with 1,586 lines:
  `Definition1`, `Theorem16`, `TridentGadget`, `OrbitStructure`,
  `OrbitLabels`, `Candidate`, `CandidateGraph` and `CandidateValid`. The
  first version says that the step from Definition 1 to the candidates, the
  paper's Lemma 6, is not formalized. Here the step is formalized, with the
  part of Lemma 6 that it needs (the orbit types, `orbit_structure`), and
  Theorem 16 is stated for Definition 1.
- Added: `atlas/Meaning.lean` and Statements 5–7. They restate the
  composition lemmas of `Proofs`, the action lemmas of `ProofsAction` and
  the orbit lemmas of `ProofsOrbit`, and state what `gadgetK` decides.
- Added: `checks/ProofCone.lean` (the dependency check) and `report/`.
- Renamed: Statements 3 and 4 are named by the number of auxiliary
  vertices. In the first version they are
  `no_valid_symmetric_gadget_below_12_vertices` and
  `valid_symmetric_gadget_up_to_12_vertices_is_trident`. The statements
  themselves are the same.
- Removed: the declarations that no statement uses. These include the
  older N ≤ 9 theorem with its six sweeps of the compositions of sizes 1 and
  2 (the sweep of `[3]` is kept), the multi-clause check, the raw walk, the
  audit summaries and the `atlas-sweep` executable. The files `Audit`,
  `Gadgets`, `Report`, `Sweep` and `SliceOrder` are gone.
- Comments: the first version's comments name the development stages of
  the authors' larger framework ("P3", "P4 stage 2"). Here they name the
  files and theorems of this package. The header of `atlas/Atlas.lean` now
  relates the number of candidates to the paper's Table 1.
- Wording of the README: the first version's README calls the engine's
  candidate space "the paper's candidate space (Definition 1) plus two more
  switches". There "the paper's candidate space" means the candidates of the
  paper's enumeration, which have no edge from a literal to G_T or G_F.
  Definition 1 by itself allows such an edge. This README therefore says
  that the engine's candidates are the gadgets of Definition 1 and that the
  paper's enumeration has two switches fewer (see "The candidate space and
  the paper's Table 1"). The space is the same in both versions.
- Unchanged: every remaining declaration and proof.
