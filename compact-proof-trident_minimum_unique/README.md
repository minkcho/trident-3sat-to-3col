# Compact Lean 4 proof: the trident as the minimum S3-symmetric clause gadget

A machine-checked proof, in Lean 4 with Mathlib, of Theorem 16 of the paper
for candidates with at most twelve vertices: among the S3-symmetric clause
gadgets for the reduction from 3SAT to 3-coloring, none has fewer than six
auxiliary vertices, and with six the only one is the trident.

This package is the proof of `../trident-symmetric-gadget-proof/` cut down to
what its statements use, with three statements added that say what the
engine functions in those statements mean. The report
[`report/proof-report.pdf`](report/proof-report.pdf) explains the
statements, follows the proof, and lists the trusted base and what is not
formalized.

The candidates carry the standard S3 action on each orbit. That every gadget
of the paper's Definition 1 has this form follows from the paper's Lemma 6
(orbit structure) and is not formalized.

The formal verification was written with Claude (Anthropic) and is under
evaluation by the authors. It is not part of the paper, which proves
Theorem 16 by the argument of its Section IV.

## For reviewers

You do not need to read the proofs, because Lean checks them. What needs
checking is that the statements say what the paper claims.

1. Read [`atlas/Statement.lean`](atlas/Statement.lean), 135 lines. It
   gives the seven statements in one place (see below).
2. Read the definitions these statements use: 76 declarations, 349 lines.
   The ranges below also include the comments between them.

   | file | lines | what |
   |---|---|---|
   | `atlas/Atlas.lean` | 29–45, 49–74, 78–105, 147–172 | S3 permutations, vertices, the S3 action, candidate edges, orbit compositions |
   | `atlas/Framework.lean` | 16–57, 61–75, 79–130 | instances, the problem interface, the eight-row validity check `gadgetK` |
   | `atlas/Kits.lean` | 21–35 | the feasibility kit |
   | `atlas/Problems/ThreeColoring.lean` | 16–58 | the 3-coloring check and the palette |
   | `atlas/ProofsDecide.lean` | 90–108 | the trident under its two labelings (`tridentA`, `tridentB`) |
   | `atlas/Statement.lean` | 35–41 | `SymCandidate` |
   | `atlas/ProofsColor.lean` | 28–39 | `SpecExt`: a proper coloring that respects the pins (Statement 7) |
   | `atlas/ProofsSym.lean` | 637–641, 817–822 | `rowPins`, `rowInst`: the instance of one input row (Statement 7) |
   | `atlas/ProofsColorK.lean` | 23–31 | `colorAt`, `combined`, used by `SpecExt` |
   | `atlas/ProofsOrbit.lean` | 29–41, 69–77 | `S3` as a group, `LegalUniverse` (Statement 6) |
   | `atlas/ProofsAction.lean` | 92–94, 425–427 | `Universe.legal`, `pinv` (Statement 6) |

   Statements 1–4 alone use 56 of these declarations (257 lines), all in
   the first six rows. The table leaves out three proofs that these
   definitions refer to: `id_mem_perms` (`ProofsAction.lean`, line 35),
   `instLawfulBEqVertex` (`ProofsAction.lean`, lines 256–279) and
   `attach_legal` (`ProofsSym.lean`, lines 209–218). Lean checks them, and
   they do not change what the definitions mean. The same holds for the
   group laws inside the `Group` instance of `S3`.
3. Run `lake exe cache get` and then `lake build`. The build checks every
   proof and prints the axioms of the seven statements. The first build
   takes about 8.5 hours, almost all of it in `ProofsSweeps16` (six
   `native_decide` re-runs on one thread); later builds reuse the result and
   take seconds.

## What is proved

`atlas/Statement.lean`:

1. `trident_is_symmetric_candidate`: the trident is an S3-symmetric
   candidate of composition `[3, 3]`.
2. `trident_is_valid`: the trident is a valid clause gadget, on all eight
   inputs.
3. `no_valid_symmetric_gadget_below_12_vertices`: no valid S3-symmetric
   candidate has at most five auxiliary vertices (N ≤ 11).
4. `valid_symmetric_gadget_up_to_12_vertices_is_trident`: every valid
   S3-symmetric candidate with N ≤ 12 has composition `[3, 3]` and is the
   trident, under one of its two labelings.
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

Statements 5–7 connect the engine functions in Statements 1–4 to their
meaning. With them, Statements 3 and 4 say that among the S3-symmetric
candidates with at most twelve vertices, the only valid clause gadgets are
the two labelings of the trident.

## Trusted base

- Lean's kernel and the standard axioms `propext`, `Classical.choice`,
  `Quot.sound`.
- Mathlib v4.33.0.
- The compiler, for seven `native_decide` re-runs of the search: six empty
  sweeps in `ProofsSweeps16.lean` and `trident_slice_found` in
  `ProofsDecide.lean`. Statements 3 and 4 depend on them; Statements 1, 2
  and 5–7 do not. The sweep of `[3]` is checked by the kernel.

## What is not formalized

- The passage from the paper's Definition 1 to the candidate space (Lemma 6
  and a relabeling of each orbit).
- That `tridentA` and `tridentB` are the same graph up to relabeling the
  parts. This is read off the definitions.
- The candidate and leaf counts in the paper's Table 1, which come from the
  enumeration program in the parent folder.

## Dependency check

`checks/ProofCone.lean` follows types, definition bodies and proofs from the
seven statements and lists every declaration of the package that is never
reached. Run it in the built package:

```
lake env lean checks/ProofCone.lean
```

It reports 445 declarations, 346 used. All 99 unused declarations are
generated by Lean (recursors, derived instances, two structure projections,
one congruence lemma). No declaration written in the source is unused.

## Differences from `trident-symmetric-gadget-proof`

- Removed: the declarations that no statement uses. These include the
  N ≤ 9 sweeps, the multi-clause check, the raw walk, the audit summaries
  and the `atlas-sweep` executable. The files `Audit`, `Gadgets`, `Report`,
  `Sweep` and `SliceOrder` are gone.
- Added: `atlas/Meaning.lean` and Statements 5–7. They connect the
  composition lemmas and the S3-action lemmas of `ProofsOrbit` to the
  statements, and state what `gadgetK` decides.
- Unchanged: every remaining declaration and proof.
