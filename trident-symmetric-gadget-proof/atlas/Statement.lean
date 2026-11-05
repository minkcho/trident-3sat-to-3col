import atlas.ProofsTheorem16

/-!
  # What this project proves (start here)

  This file restates the results in one place. `lake build` checks every
  statement below together with the proofs in the other files; a reviewer
  does not need to read those proofs. The definitions the statements use are
  listed in README.md, section "For reviewers".

  Notation.
  - `compositions k [1, 2, 3, 6]` lists the orbit compositions of `k`
    auxiliary vertices: the multisets of orbit sizes 1, 2, 3, 6 summing to
    `k`, each written in non-decreasing order. The candidate has
    N = k + 6 vertices.
  - `threeColoring.attach parts` builds the candidate space of the orbit
    composition `parts`. Its vertices are the literals x0, x1, x2, the
    auxiliary orbits (sizes `parts`) and the palette anchors G_T, G_F, G_B.
    `.1.edges` lists the switchable pairs: every pair except
    literal–literal. `.2` lists the forced edges: the palette triangle and
    the G_B fan.
  - `gadgetK threeColoring parts g false` judges `g` on all eight literal
    inputs. It is `some 1` when `g` is a valid clause gadget, i.e. a proper
    3-coloring extending the pins exists exactly for the satisfying inputs.
    It is `none` when `g` is not valid.
  - `tridentA` and `tridentB` are the trident, with either size-3 orbit as
    the branch layer.
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

/-- 1. The trident is an S3-symmetric candidate of composition `[3, 3]`
    (N = 12 vertices). -/
theorem trident_is_symmetric_candidate : SymCandidate [3, 3] tridentA := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- 2. The trident is a valid clause gadget, judged on all eight inputs. -/
theorem trident_is_valid : gadgetK threeColoring [3, 3] tridentA false = some 1 := by
  decide

/-- 3. Minimality: no S3-symmetric candidate with at most five auxiliary
    vertices (N ≤ 11) is a valid clause gadget. -/
theorem no_valid_symmetric_gadget_below_12_vertices :
    ∀ k, k ≤ 5 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g → gadgetK threeColoring parts g false = none :=
  fun k hk parts hparts g ⟨hsub, hinv, hforced⟩ =>
    no_symmetric_gadget_below_six k hk parts hparts g hsub hinv hforced

/-- 4. Uniqueness: every valid S3-symmetric candidate with at most six
    auxiliary vertices (N ≤ 12) has composition `[3, 3]`, budget 1, and the
    edge set of the trident under one of its two labelings. -/
theorem valid_symmetric_gadget_up_to_12_vertices_is_trident :
    ∀ k, k ≤ 6 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g →
      ∀ b, gadgetK threeColoring parts g false = some b →
        parts = [3, 3] ∧ b = 1 ∧
          ((∀ e, e ∈ g ↔ e ∈ tridentA) ∨ (∀ e, e ∈ g ↔ e ∈ tridentB)) :=
  fun k hk parts hparts g ⟨hsub, hinv, hforced⟩ =>
    trident_minimum_unique k hk parts hparts g hsub hinv hforced

end Atlas.Statement

-- The axioms each statement rests on. `lake build` prints them.
#print axioms Atlas.Statement.trident_is_symmetric_candidate
#print axioms Atlas.Statement.trident_is_valid
#print axioms Atlas.Statement.no_valid_symmetric_gadget_below_12_vertices
#print axioms Atlas.Statement.valid_symmetric_gadget_up_to_12_vertices_is_trident
