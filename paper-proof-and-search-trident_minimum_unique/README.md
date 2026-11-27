# Theorem 16 by the paper's proof, and the search tied to it, in Lean 4

A machine-checked development, in Lean 4 with Mathlib, in two parts.

- [`proof/`](proof) proves Theorem 16 of the paper by the paper's own
  argument (Section IV), lemma by lemma: every valid S3-symmetric clause
  gadget for the reduction from 3SAT to 3-coloring, on a finite vertex set,
  has at least six auxiliary vertices, and one with six is the trident. It
  uses Mathlib only.
- [`search/`](search) holds an exhaustive search for valid gadgets (the
  candidate space, the judge and the search procedure) and ties it to
  Definition 1 and to Theorem 16. The candidate space is exactly the set of
  gadgets of Definition 1 on finite vertex sets, the search procedure finds
  every valid candidate and reports only valid candidates, and what the
  search returns follows from Theorem 16. The search is the engine of
  `../trident-symmetric-gadget-proof/`. It is not the enumeration program of
  the paper's Section IV-D; "Remarks on the search" states the difference.

No statement uses a run of the search or compiled code. Every result depends
on Lean's three standard axioms only, and the package builds in less than a
minute once Mathlib is in place.

A gadget of Definition 1 has six fixed vertices, the three literals (the
input) and the palette triangle (the fixed colors), and auxiliary vertices.
The results count the auxiliary vertices added to these six. They are not
about arbitrary graphs with at most twelve vertices.

The formal verification was written with Claude (Anthropic) and is under
evaluation by the authors. It is not part of the paper.

## For reviewers

You do not need to read the proofs, because Lean checks them. What needs
checking is that the statements say what the paper claims.

1. Read [`proof/Definition1.lean`](proof/Definition1.lean), 97 lines. It
   uses Mathlib only. It defines an S3-symmetric clause gadget (`Gadget`),
   its auxiliary vertices (`Gadget.IsAux`), its validity (`Gadget.Extends`,
   `Gadget.Valid`) and the trident graph (`TV`, `tridentEdge`, `trident`).
2. Read the two theorems at the end of
   [`proof/Theorem16.lean`](proof/Theorem16.lean):
   - `trident_is_valid_gadget`: the trident is a valid S3-symmetric clause
     gadget with six auxiliary vertices (twelve vertices in total);
   - `minimum_unique`: every valid S3-symmetric clause gadget on a finite
     vertex set has at least six auxiliary vertices, added to its six fixed
     vertices, and one with exactly six is isomorphic to the trident by an
     isomorphism that fixes each literal and each anchor.

   These two statements use only the seven definitions of step 1.
3. Read [`search/Statement.lean`](search/Statement.lean), about 430 lines.
   It lists the statements about the search. They are described below. Its
   last 110 lines only check axioms.
4. Run `lake exe cache get` and then `lake build`. The build checks every
   proof and prints the axioms of the two theorems: `propext`,
   `Classical.choice` and `Quot.sound`. It fails if one of the following
   depends on any other axiom: the two theorems, a statement of
   `search/Statement.lean`, or one of five further results of Part 1
   (`Gadget.lemma6`, `Gadget.fiber_card`, `ClauseGadget.lemma11`,
   `Gadget.toClauseGadget_spec`, `iso_of_literal_set`). The checks are
   `#guard_msgs` commands at the ends of the files. Every other declaration
   written in the package is used by one of these 26 results.

## Part 1: the paper's proof (`proof/`)

Every numbered statement of the paper's Sections IV-A to IV-C is stated and
proved in Lean, and so is the remark after Theorem 16. The names are in the
namespace `Def1`.

| paper | file | Lean name |
|---|---|---|
| Definition 1 | `Definition1.lean` | `Gadget`, `Gadget.IsAux`, `Gadget.Extends`, `Gadget.Valid` |
| Theorem 4 (the trident is valid) | `TridentGadget.lean` | `tridentGadget_valid` |
| no edge from a literal to G_T or G_F (after Definition 1) | `Basics.lean` | `Gadget.Valid.noLitAnchor` |
| Lemma 6 (orbit structure) | `Lemma6.lean` | `Gadget.lemma6` |
| Definition 2 and Claim 1 (fibers) | `Definition2.lean` | `Gadget.fiber`, `Gadget.fiber_card` |
| Lemma 7 (size-2 orbit reduction) | `Lemma7.lean` | `Gadget.lemma7` |
| Lemma 8 (color-swap symmetry) | `Lemma8.lean` | `Gadget.lemma8` |
| Corollary 9 (anchor normalization) | `Corollary9.lean` | `Gadget.cor9_i`, `Gadget.cor9_ii` |
| Lemma 10 (mimicry) and Claim 2 (palettes) | `Lemma10.lean` | `Gadget.lemma10`, `Gadget.palette_claim` |
| Lemma 11 (the degree-one channel) | `Lemma11.lean` | `Gadget.lemma11`, `Gadget.lemma11_containment` |
| Lemma 11 for arbitrary clause gadgets (the remark in its proof) | `ClauseGadget.lean` | `ClauseGadget.lemma11`, `ClauseGadget.noLitAnchor` |
| Corollary 12 | `Corollary12.lean` | `Gadget.cor12` |
| Lemma 13 (matched base extensions) | `Lemma13.lean` | `Gadget.lemma13` |
| Lemma 14 (two isolated layers) | `Lemma14.lean` | `Gadget.lemma14` |
| the triangle analysis after Lemma 14 | `TriangleAnalysis.lean` | `Gadget.no_disconnected_layer`, `Gadget.triangle_analysis` |
| Lemma 15 (free orbit exclusion) | `Lemma15.lean` | `Gadget.lemma15` |
| Theorem 16 | `Theorem16.lean` | `Gadget.minimum_is_trident`, `minimum_unique` |
| the remark after Theorem 16 (the isomorphism is unique) | `Uniqueness.lean` | `trident_rigid`, `iso_trident_unique`, `iso_trident_equivariant`, `iso_of_literal_set` |

Four files support the chain. `Basics.lean` holds the anchors as a family,
colorings, inputs, recoloring and counting. `Removal.lean` removes a set of
auxiliary vertices from a gadget; it gives the merge of Corollary 9(ii) and
the deletion of a disconnected layer. `TwoLayers.lean` indexes the twelve
vertices of a gadget with two size-3 orbits and describes its edges by the
attachments of Lemma 6. `OrbitStructure.lean` has the group theory of
Lemma 6.

### How the proof goes

As in the paper, let `G` be a valid gadget with the minimum number of
auxiliary vertices (`Gadget.IsMinimum`, `Gadget.minimum_is_trident`). It has
at most six, since the trident is valid.

- **Required first layer.** A free orbit would use all six auxiliary vertices
  and be the sole auxiliary orbit, which Lemma 15 excludes. By Lemma 11 some
  auxiliary vertex has exactly one literal neighbor, and by Lemma 6 its
  orbit is then a size-3 orbit with a matched attachment. This orbit is
  isolated by Corollary 12: it is the matched base.
- **Remaining budget.** If the other auxiliary vertices do not form a second
  size-3 orbit, they are singletons, possibly with one size-2 orbit. Lemma 7
  turns the size-2 orbit into two singletons, and Lemma 13 excludes the
  family.
- **Equality case.** A second size-3 orbit uses all six vertices. Two
  isolated layers are excluded by Lemma 14, and the triangle analysis leaves
  the trident.

`minimum_unique` follows: the minimum is six, and a valid gadget with six
auxiliary vertices is a minimum one.

### Remarks from the formalization

- Every step of the paper's proof of Theorem 16 is formalized, in the
  paper's order, and no gap was found in it. The Lean proofs differ from the
  text in the details listed below.
- Lemma 6 is proved as one statement (`Gadget.lemma6`), but no other proof
  uses it in this form. The proofs use its parts: the four stabilizers of a
  vertex (`Gadget.stab_cases`), the literal neighbors of a vertex that the
  even permutations fix (`Gadget.adj_lit_of_even_fixed`), and the edges of a
  size-3 orbit (`Gadget.Layer.adj_self`, `Gadget.Layer.adj_lit`). Part 2
  uses the orbit types (`orbit_structure` in `OrbitStructure.lean`).
- Two hypotheses are not used by the formal proofs. Lemma 13 does not use
  that the attachment of the matched base is not crossed. Lemma 15 does not
  use that the orbit is free, only that it is the sole auxiliary orbit.
- The proof of Lemma 13 uses a singleton only through the even permutations,
  which fix it. The same argument therefore covers orbits of size 2
  (`Gadget.lemma13_of_even_fixed`), and with this form the "remaining
  budget" step would not need Lemma 7. The package follows the paper: it
  proves Lemma 7 and applies Lemma 13 as stated.
- Lemma 14 is stated for two disjoint size-3 orbits of a minimum valid
  gadget. That they are all the auxiliary vertices follows from the budget
  (`Gadget.two_layers_exhaust_budget`).
- The case `d = 0` of the triangle analysis is proved for any second layer
  without an edge to the rest (`Gadget.no_disconnected_layer`): the layer is
  deleted, and Lemma 13 excludes what is left. In the words of the paper, a
  disconnected second layer cannot repair the matched base.
- Corollary 9(ii) is applied where it is needed, in Lemma 14, in Lemma 15
  and for the anchors of the branch layer, not as a first step of the proof
  of Theorem 16.
- Claim 1 (fibers) is proved by counting the two permutations that move one
  index to another, not by the edge-orbit argument of the paper. Theorem 16
  does not need fibers: the proof of Lemma 15 uses the literal neighbors of
  the two ends of an internal edge directly.
- Claim 2 (palettes) uses the standing assumption of the paper's Section IV-A
  that no edge joins a literal to G_T or G_F. The Lean statement names it
  as a hypothesis, and Lemma 11 obtains it from validity.
- The remark at the end of the proof of Lemma 11, that the lemma holds for
  arbitrary clause gadgets, is proved in `ClauseGadget.lean` for the graph
  of Definition 1 without the action. The standing assumption is proved
  there without symmetry: an edge from a literal to G_T rejects the input in
  which only this literal is true, and an edge from a literal to G_F rejects
  a satisfying input in which this literal is false.

## Part 2: the search (`search/`)

The search works on a candidate space. For an orbit
composition `parts`, a candidate is an edge list on the vertices of the
composition and the palette that is closed under the S3 action and contains
the forced edges (`SymCandidate parts g`). The judge `gadgetK` tests a
candidate on the eight inputs. The search procedure `searchSlice` walks the
subsets of the free edge orbits of a composition depth first. It may skip a
subtree in which a satisfiable input has become uncolorable (pruning). It
tests each graph that it reaches on four inputs, one for each number of true
literals, and collects those that pass in the list `found`.

The statements of [`search/Statement.lean`](search/Statement.lean):

**The candidate space is the set of gadgets of Definition 1.**
- `gadget_is_candidate`: every gadget of Definition 1 on a finite vertex
  set, valid or not, is a candidate after a relabeling of its vertices, and
  it is valid exactly when the candidate passes the judge. In detail: the
  relabeling is a bijection onto the vertices of the candidate space, keeps
  the literals and the anchors, commutes with the two actions, and turns
  adjacency into membership in an edge list, and this edge list is a
  candidate. The orbit composition is in the list
  `compositions k [1, 2, 3, 6]`, over which the statements about the search
  range. The proof uses the orbit types of the paper's Lemma 6
  (`orbit_structure`).
- `candidate_is_gadget`: every candidate is a gadget of Definition 1 with as
  many auxiliary vertices as its composition counts, and it passes the judge
  exactly when the gadget is valid.

**Theorem 16 in the candidate space.**
- Statements 1 and 2: the trident, under its two labelings `tridentA` and
  `tridentB`, is a candidate of the composition `[3, 3]` and passes the
  judge.
- Statement 3, `no_valid_symmetric_gadget_below_six_auxiliary_vertices`: no
  candidate with at most five auxiliary vertices passes the judge.
- Statement 4,
  `valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident`: a
  candidate with at most six auxiliary vertices that passes the judge has
  composition `[3, 3]` and the edge set of `tridentA` or of `tridentB`.

  Statements 3 and 4 follow from `minimum_unique` through the gadget of a
  candidate (`Candidate.valid_iff` and `Candidate.card_aux`, the facts that
  `candidate_is_gadget` collects). Statement 4 also uses that the
  isomorphism onto the trident commutes with the actions
  (`iso_trident_equivariant`).

**The search procedure finds every valid candidate and reports only valid candidates.**
- `search_finds_every_valid_candidate`: for every candidate that passes the
  judge, the list `found` of the search of its composition contains an edge
  list with the same edge set.
- `search_finds_only_valid_candidates`: every graph in `found` is a candidate
  that passes the judge.
- `search_finds_every_valid_gadget`: so every valid gadget of Definition 1
  on a finite vertex set is found by the search, in the same sense.

  The search does not visit every candidate: pruning skips candidates, and
  the graphs that the search reaches are tested on four of the eight inputs.
  The first statement says that no valid candidate is lost by this. Pruning
  loses nothing because adding edges never makes an uncolorable input
  colorable, and on an S3-symmetric candidate the four inputs decide the
  eight. The statements are proved by induction on the walk of the search.

**What the search returns.**
- `search_finds_nothing_below_six`: on every orbit composition with at most
  five auxiliary vertices, `found` is empty.
- `search_finds_only_the_trident`: on the compositions with at most six
  auxiliary vertices, whatever is found lies on `[3, 3]` and has the edge set
  of `tridentA` or of `tridentB`.
- `search_finds_the_trident`: both labelings are found.
- `search_finds_nothing_at_six_outside_trident_slice`: with six auxiliary
  vertices, `found` is empty on every composition other than `[3, 3]`.
- `sym_empty_13`, `sym_empty_23`, `sym_empty_113`, `sym_empty_6`,
  `sym_empty_123`, `sym_empty_1113`: the search finds nothing on these six
  compositions.

### Relation to the search-based package

`../trident-symmetric-gadget-proof/` contains the same search engine. It
obtains its Statements 3 and 4 (there
`no_valid_symmetric_gadget_below_12_vertices` and
`valid_symmetric_gadget_up_to_12_vertices_is_trident`) by running the search
at build time: the six statements `sym_empty_…` and the result of the
`[3, 3]` sweep are evaluated by compiled code (`native_decide`), which takes
about 9 hours and adds the compiler to the trusted base. Here the six
statements have the same names and the same wording, and they are
consequences of Theorem 16. The search is not run, and the build takes
seconds.

So the order of the argument is reversed. In that package the search proves
the theorem. In this one the theorem, proved by the paper's argument,
determines what the search can return, and the proved completeness of the
search says that the search would have found any other valid gadget.

The README of that package calls the engine's candidate space "the paper's
candidate space (Definition 1) plus two more switches", the literal–G_T and
the literal–G_F orbit. There "the paper's candidate space" means the
candidates of the paper's enumeration: the gadgets of Definition 1 without
an edge from a literal to G_T or G_F, which the paper excludes by the remark
after Definition 1. Definition 1 by itself allows such an edge. So the two
READMEs describe the same space. The engine's candidates are the gadgets of
Definition 1 (`gadget_is_candidate`, `candidate_is_gadget`), and the paper's
enumeration covers those in which the two orbits are switched off.

### Definitions needed to read the statements

The statements of Part 2 speak about the engine. To check them, read the
definitions they use: 89 declarations, 590 lines. Four of them are the
definitions of `Definition1.lean` from step 1 (36 lines). The other 85 are
in `search/` (554 lines) and are listed below. The search program itself is
in the first three rows.

| file | lines | what |
|---|---|---|
| `search/Atlas.lean` | 29–45, 49–74, 78–130, 147–172 | permutations, vertices, the action, candidate edges, edge orbits, compositions |
| `search/Framework.lean` | 16–57, 61–75, 79–130, 134–195 | instances, the problem interface, the judge `gadgetK`, the search `searchSlice` |
| `search/Kits.lean`, `search/Problems/ThreeColoring.lean` | 21–35; 16–58 | the feasibility kit; the 3-coloring check and the palette |
| `search/Space.lean` | 16–22 | `SymCandidate` |
| `search/Trident.lean` | 17–35 | `tridentA`, `tridentB` |
| `search/CandidateGadget.lean` | 57–246, in parts | `Candidate` and its gadget (`candidate_is_gadget`) |
| `search/Candidate.lean`, `search/CandidateGraph.lean`, `search/OrbitLabels.lean` | in parts | `parts`, `toVertex`, `edgeList`, `toTable` (`gadget_is_candidate`) |
| `search/ProofsColor.lean`, `search/ProofsColorK.lean`, `search/ProofsSym.lean` | 28–39; 23–31; 636–640, 816–821 | `SpecExt`, `rowPins`, `rowInst` (the meaning of the judge in `Space.lean`) |

The table leaves out one proof that these definitions refer to:
`instance : LawfulBEq Vertex` (`search/ProofsAction.lean`, lines 254–277).
Three more proofs lie inside the listed ranges: `Candidate.lit_mem`,
`Candidate.anchor_mem` and `Gadget.orb_data`. Lean checks all four, and they
do not change what the definitions mean.

### Remarks on the search

- The search in this package is the engine of
  `../trident-symmetric-gadget-proof/`. It is not the program
  `../Sweep.lean`, whose run the paper reports in Section IV-D, and the two
  do not enumerate the same candidates. For each of the 24 orbit
  compositions with at most six auxiliary vertices, the engine has two
  switches more than the paper's Table 1 counts: the literal–G_T orbit and
  the literal–G_F orbit. Definition 1 allows these edges, and the paper's
  enumeration leaves them out by the remark after Definition 1. So the
  engine has four times as many candidates, for example 2^16 for `[3, 3]`,
  where Table 1 lists 2^14. Only the engine is the subject of the theorems.
- `search_finds_the_trident` and `search_finds_only_the_trident` describe the
  list `found` of the `[3, 3]` sweep by the edge sets of its entries. They
  do not say that the list has exactly two entries, or in which order.

## Trusted base

- Lean's kernel and the standard axioms `propext`, `Classical.choice`,
  `Quot.sound`.
- Mathlib v4.33.0.

There is no `native_decide`. The proofs use `decide`, which the kernel
evaluates, for small concrete facts only.

- In `proof/`: facts about the three colors, the three indices, the two
  signs of a permutation and the truth values of an input; the explicit
  colorings of the trident and the numbers of its vertices; the neighbors of
  a vertex in the trident (`Uniqueness.lean`).
- In `search/`: checks of the engine's hand-written tables of the six
  permutations (closure, inverses, parity, and which permutations fix the
  first vertex of a part); the encoding of the eight inputs, the action of
  the six permutations on them and its four classes; the comparison of the
  edge lists `tridentA` and `tridentB` with the trident graph, that these
  two lists are candidates, and the verdict of the judge on them;
  memberships and inequalities of small numbers and lists.

No `decide` enumerates candidates of the search.

## What is not formalized

- The candidate and leaf counts of the paper's Table 1, which come from the
  enumeration program in the parent folder.
- That the list `found` of the `[3, 3]` sweep has exactly two entries.
- The other results of the paper.

## Dependency check

`checks/ProofCone.lean` follows types, definition bodies and proofs from the
results of the package and lists every declaration that is never reached.
Run it in the built package:

```
lake env lean checks/ProofCone.lean
```

It reports 869 declarations, 708 used. No declaration written in the source
is unused. The other 161 are generated by Lean: recursors and other
constructions for structures and inductive types, derived instances, and the
projections of structure fields that no result reads.

## Files

- `proof/`: 21 files, 3,749 lines.
- `search/`: 28 files, 6,350 lines. The engine and its lemmas come from
  `../trident-symmetric-gadget-proof/`, cut down to the declarations that
  the statements use.
