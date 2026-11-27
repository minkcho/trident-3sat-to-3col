# The paper's own proof of Theorem 16, in Lean 4

A machine-checked proof, in Lean 4 with Mathlib, of Theorem 16 of the paper
that follows the paper's own argument (Section IV) lemma by lemma: every
valid S3-symmetric clause gadget for the reduction from 3SAT to 3-coloring
has at least six auxiliary vertices, and one with six is the trident.

The proof uses no search and no compiled code. The theorem depends on Lean's
three standard axioms only. Once Mathlib is in place, the package builds in
less than a minute.

The statement is the one of `../compact-proof-trident_minimum_unique/`: the
same file `Definition1.lean` and the same theorem `minimum_unique`. That
package proves it through an exhaustive search. This package proves it by
the lemma chain of the paper. The two proofs share the statement, the orbit
types of Lemma 6 (`OrbitStructure.lean`) and the validity of the trident
(`TridentGadget.lean`), and nothing else.

A gadget of Definition 1 has six fixed vertices, the three literals (the
input) and the palette triangle (the fixed colors), and auxiliary vertices.
The result counts the auxiliary vertices added to these six. It is not
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
3. Run `lake exe cache get` and then `lake build`. The build checks every
   proof and prints the axioms of the two theorems: `propext`,
   `Classical.choice` and `Quot.sound`. It fails if the two theorems depend
   on any other axiom (`#guard_msgs` at the end of `Theorem16.lean`).

## The paper and the Lean files

Every numbered statement of the paper's Sections IV-A to IV-C is stated and
proved in Lean. The names are in the namespace `Def1`.

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

The proof uses Lemma 6 through its parts: the orbit types
(`orbit_structure` in `OrbitStructure.lean`, `Gadget.stab_cases`), the two
vertices of a size-2 orbit (`Gadget.sign_orbit`), the literal neighbors of a
vertex of a size-1 or size-2 orbit (`Gadget.adj_lit_of_even_fixed`), and the
edges of a size-3 orbit (`Gadget.Layer.adj_self`, `Gadget.Layer.adj_lit`).

Three files support the chain. `Basics.lean` holds the anchors as a family,
colorings, inputs, recoloring and counting. `Removal.lean` removes a set of
auxiliary vertices from a gadget; it gives the merge of Corollary 9(ii) and
the deletion of a disconnected layer. `TwoLayers.lean` indexes the twelve
vertices of a gadget with two size-3 orbits and describes its edges by the
attachments of Lemma 6.

`Definition1.lean` and `OrbitStructure.lean` are the files of the compact
package, byte for byte, and `TridentGadget.lean` differs in its import line
only. Their comments mention the search engine of the compact package, which
this package does not contain.

## How the proof goes

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

## Remarks from the formalization

- Every step of the paper's proof of Theorem 16 is formalized, in the
  paper's order, and no gap was found in it. The Lean proofs differ from the
  text in the details listed below.
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

## Trusted base

- Lean's kernel and the standard axioms `propext`, `Classical.choice`,
  `Quot.sound`.
- Mathlib v4.33.0.

There is no `native_decide`. The proofs use `decide`, which the kernel
evaluates, for small concrete facts only:

- facts about the three colors, the three indices, the two signs of a
  permutation and the truth values of an input, for example that a triangle
  cannot be colored with two colors;
- in `TridentGadget.lean`, that the explicit colorings of the trident are
  proper, and the numbers of its vertices and of its auxiliary vertices.

No `decide` enumerates gadgets or permutations. The orbit types are obtained
from Lagrange's theorem and the orbit-stabilizer theorem, as in the paper.

## What is not formalized

- The paper's remark after Theorem 16 that the isomorphism onto the trident
  is unique and commutes with the two S3-actions. `minimum_unique` gives the
  existence of the isomorphism only.
- The exhaustive enumeration of the paper's Section IV-D and the counts of
  its Table 1.
- The other results of the paper.

## Dependency check

`checks/ProofCone.lean` follows types, definition bodies and proofs from the
two theorems of `Theorem16.lean` and from the statements of the paper that
the theorems do not use as stated: `Gadget.lemma6`, `Gadget.fiber_card`, and
`ClauseGadget.lemma11` with `Gadget.toClauseGadget_spec`. It lists every
declaration of the package that is never reached. Run it in the built
package:

```
lake env lean checks/ProofCone.lean
```

It reports 314 declarations, 252 used. One declaration written in the
source is not used: `exists_orbit_labeling` in `OrbitStructure.lean`, which
the compact package uses. The other 61 are generated by Lean; among them
are the projections of two fields of `ClauseGadget` that Lemma 11 does not
read (`palette` and `fan`).

## Files

20 files in `proof/`, 3,560 lines. 17 of them, 3,145 lines, are specific to
this package; the other three are shared with the compact package.
