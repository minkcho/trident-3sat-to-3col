# Compact Lean 4 proof: the trident as the minimum S3-symmetric clause gadget

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

The proof has two layers. The paper's Lemma 6 (orbit structure) turns a
gadget of Definition 1 into a candidate of a search engine. In the engine's
candidate space the result follows from two proved reductions and an
exhaustive search whose runs are repeated at build time, seven of them by
compiled code (see "Trusted base"). The second layer is the proof of
`../trident-symmetric-gadget-proof/` cut down to what its statements use.

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
   statements below. The first build takes about 8.5 hours, almost all of it
   in `ProofsSweeps16` (six `native_decide` re-runs on one thread); later
   builds reuse the result and take seconds.

### The intermediate statements

[`atlas/Statement.lean`](atlas/Statement.lean), 137 lines, gives seven
statements about the engine's candidate space. They are steps of the proof
and are not needed to know what is proved. To check them as well, read the
definitions they use: 76 declarations, 349 lines. The ranges below also
include the comments between them.

| file | lines | what |
|---|---|---|
| `atlas/Atlas.lean` | 29–45, 49–74, 78–105, 147–172 | S3 permutations, vertices, the S3 action, candidate edges, orbit compositions |
| `atlas/Framework.lean` | 16–57, 61–75, 79–130 | instances, the problem interface, the eight-row validity check `gadgetK` |
| `atlas/Kits.lean` | 21–35 | the feasibility kit |
| `atlas/Problems/ThreeColoring.lean` | 16–58 | the 3-coloring check and the palette |
| `atlas/ProofsDecide.lean` | 90–108 | the trident under its two labelings (`tridentA`, `tridentB`) |
| `atlas/Statement.lean` | 37–43 | `SymCandidate` |
| `atlas/ProofsColor.lean` | 28–39 | `SpecExt`: a proper coloring that respects the pins (Statement 7) |
| `atlas/ProofsSym.lean` | 637–641, 817–822 | `rowPins`, `rowInst`: the instance of one input row (Statement 7) |
| `atlas/ProofsColorK.lean` | 23–31 | `colorAt`, `combined`, used by `SpecExt` |
| `atlas/ProofsOrbit.lean` | 29–41, 69–77 | `S3` as a group, `LegalUniverse` (Statement 6) |
| `atlas/ProofsAction.lean` | 92–94, 425–427 | `Universe.legal`, `pinv` (Statement 6) |

Statements 1–4 alone use 56 of these declarations (257 lines), all in the
first six rows. The table leaves out three proofs that these definitions
refer to: `id_mem_perms` (`ProofsAction.lean`, line 35),
`instLawfulBEqVertex` (`ProofsAction.lean`, lines 256–279) and
`attach_legal` (`ProofsSym.lean`, lines 209–218). Lean checks them, and they
do not change what the definitions mean. The same holds for the group laws
inside the `Group` instance of `S3`.

## What is proved

For the paper's Definition 1 (`atlas/Theorem16.lean`):

- `trident_is_valid_gadget`: the trident graph, with its literals and
  anchors, carries an S3-symmetric clause gadget, this gadget is valid (the
  paper's Theorem 4), and it has six auxiliary vertices, the p_i and the
  u_i (twelve vertices in total).
- `minimum_unique`: Theorem 16, as described above.

The paper's Lemma 6, in `atlas/OrbitStructure.lean` (Mathlib only):

- `orbit_structure`: an orbit of an S3 action has size 1, 2, 3 or 6 and
  carries the trivial, sign, natural or free action. The proof follows the
  paper: Lagrange's theorem, the subgroups of S3 of each order, and the
  orbit-stabilizer theorem.

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
6. `candidate_action_is_s3_action`: on every candidate, `act` is an action
   of S3 that permutes the literals naturally and fixes the three palette
   anchors. It is a Mathlib `MulAction`, and every edge orbit has size 1, 2,
   3 or 6.
7. `gadgetK_is_validity`: `gadgetK … false = some b` holds exactly when
   `b = 1` and, for each of the eight inputs, the row is 3-colorable if and
   only if the input satisfies the clause. A row is 3-colorable exactly when
   a proper coloring that respects its pins exists.

`minimum_unique` is derived from Statements 3, 4, 5 and 7: Lemma 6 gives
every gadget of Definition 1 an orbit composition and a relabeling into the
candidate space (`atlas/Candidate.lean`, `atlas/CandidateGraph.lean`), and
validity becomes the verdict of `gadgetK` (`atlas/CandidateValid.lean`).

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
edge lists `tridentA` and `tridentB` with the trident graph, and the explicit
colorings of the trident. The report lists them.

## What is not formalized

- The paper's own proof of Theorem 16 (the lemma chain of its Sections IV-B
  and IV-C). The formal proof reaches the statement by the exhaustive search
  in the candidate space. From Section IV it formalizes the orbit types of
  Lemma 6, a special case of Lemma 11 and the four-input reduction. The
  package `../own-proof-trident_minimum_unique/` formalizes the lemma chain.
- The statements of Lemma 6 about the subgraph induced on an orbit of size 3
  and about literal attachments. The proof does not need them.
- The paper's remark after Theorem 16 that the isomorphism onto the trident
  is unique and commutes with the two S3-actions. `minimum_unique` gives the
  existence of the isomorphism only.
- The candidate and leaf counts in the paper's Table 1, which come from the
  enumeration program in the parent folder.
- The other results of the paper.

## Dependency check

`checks/ProofCone.lean` follows types, definition bodies and proofs from the
two theorems of `Theorem16.lean` and the seven statements, and lists every
declaration of the package that is never reached. Run it in the built
package:

```
lake env lean checks/ProofCone.lean
```

It reports 634 declarations, 513 used. All 121 unused declarations are
generated by Lean (recursors, derived instances, generated congruence
lemmas, two structure projections). No declaration written in the source is
unused.

## Differences from `trident-symmetric-gadget-proof`

- Removed: the declarations that no statement uses. These include the
  N ≤ 9 sweeps, the multi-clause check, the raw walk, the audit summaries
  and the `atlas-sweep` executable. The files `Audit`, `Gadgets`, `Report`,
  `Sweep` and `SliceOrder` are gone.
- Added: `atlas/Meaning.lean` and Statements 5–7. They connect the
  composition lemmas and the S3-action lemmas of `ProofsOrbit` to the
  statements, and state what `gadgetK` decides.
- Added: the layer for Definition 1, eight files with 1,582 lines:
  `Definition1`, `Theorem16`, `TridentGadget`, `OrbitStructure`,
  `OrbitLabels`, `Candidate`, `CandidateGraph` and `CandidateValid`.
- Unchanged: every remaining declaration and proof.
