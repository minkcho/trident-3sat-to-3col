import search.Meaning

/-!
  The candidate space of the search.

  `SymCandidate parts g` says that the edge list `g` is an S3-symmetric
  candidate of orbit composition `parts`. The two theorems after it say what
  the list of compositions and the judge `gadgetK` are, so that statements
  about candidates can be read without the engine.
-/

namespace Atlas.Statement

open Atlas

/-- An S3-symmetric candidate of composition `parts`. The graph `g` lies
    in the candidate space, is closed under the S3 action and contains the
    forced edges. -/
abbrev SymCandidate (parts : List Nat) (g : List Edge) : Prop :=
  (∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges) ∧
  (∀ s ∈ perms, ∀ e ∈ g, (threeColoring.attach parts).1.actEdge s e ∈ g) ∧
  (∀ f ∈ (threeColoring.attach parts).2, normEdge f ∈ g)

/-- `compositions k [1, 2, 3, 6]` lists every orbit composition of `k`:
    exactly the non-decreasing lists over {1, 2, 3, 6} summing to `k`. -/
theorem compositions_are_all_orbit_compositions (k : Nat) (c : List Nat) :
    c ∈ compositions k [1, 2, 3, 6] ↔
      c.sum = k ∧ (∀ x ∈ c, x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 6) ∧ c.Pairwise (· ≤ ·) :=
  Meaning.mem_compositions_iff

/-- The judge: `gadgetK` returns `some b` exactly when `b = 1` and, for
    each of the eight inputs, the row is 3-colorable if and only if the input
    satisfies the clause (`env ≠ 0`). The row is 3-colorable exactly when
    some choice of colors (`SpecExt`) respects the pins of the row (anchors
    T, F, B; true literals T; false literals F) and gives adjacent vertices
    different colors. -/
theorem gadgetK_is_validity (parts : List Nat) (g : List Edge) (b : Nat) :
    (gadgetK threeColoring parts g false = some b ↔
      b = 1 ∧ ∀ env, env < 8 → (colorsOk (rowInst parts g env) = true ↔ env ≠ 0)) ∧
    ((∀ e ∈ g, e ∈ (threeColoring.attach parts).1.edges) → ∀ env,
      (colorsOk (rowInst parts g env) = true ↔
        ∃ f, SpecExt g (rowPins parts env) (threeColoring.attach parts).1.vertices [] f)) :=
  ⟨Meaning.gadgetK_some_iff parts g b, fun hg env => Meaning.colorsOk_rowInst_iff parts hg env⟩

end Atlas.Statement
