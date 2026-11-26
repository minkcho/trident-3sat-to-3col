import atlas.ProofsTheorem16
import atlas.Meaning

/-!
  # The statements about the candidate space

  This file restates, in one place, the results about the engine's candidate
  space. `lake build` checks every statement below together with the proofs
  in the other files; a reviewer does not need to read those proofs. The
  definitions the statements use are listed in README.md, section "For
  reviewers". `Theorem16.lean` derives from these statements the results for
  the paper's Definition 1, which are stated without the engine.

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
theorem no_valid_symmetric_gadget_below_six_auxiliary_vertices :
    ∀ k, k ≤ 5 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g → gadgetK threeColoring parts g false = none :=
  fun k hk parts hparts g ⟨hsub, hinv, hforced⟩ =>
    no_symmetric_gadget_below_six k hk parts hparts g hsub hinv hforced

/-- 4. Uniqueness: every valid S3-symmetric candidate with at most six
    auxiliary vertices (N ≤ 12) has composition `[3, 3]`, budget 1, and the
    edge set of the trident under one of its two labelings. -/
theorem valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident :
    ∀ k, k ≤ 6 → ∀ parts ∈ compositions k [1, 2, 3, 6], ∀ g : List Edge,
      SymCandidate parts g →
      ∀ b, gadgetK threeColoring parts g false = some b →
        parts = [3, 3] ∧ b = 1 ∧
          ((∀ e, e ∈ g ↔ e ∈ tridentA) ∨ (∀ e, e ∈ g ↔ e ∈ tridentB)) :=
  fun k hk parts hparts g ⟨hsub, hinv, hforced⟩ =>
    trident_minimum_unique k hk parts hparts g hsub hinv hforced

/-! ## What the statements mean

  The four statements speak about engine functions. The next three theorems
  say what those functions are (proofs in `Meaning.lean`), so the statements
  can be read without the engine. -/

/-- 5. `compositions k [1, 2, 3, 6]` lists every orbit composition of `k`:
    exactly the non-decreasing lists over {1, 2, 3, 6} summing to `k`. So
    statements 3 and 4 cover every orbit composition. -/
theorem compositions_are_all_orbit_compositions (k : Nat) (c : List Nat) :
    c ∈ compositions k [1, 2, 3, 6] ↔
      c.sum = k ∧ (∀ x ∈ c, x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 6) ∧ c.Pairwise (· ≤ ·) :=
  Meaning.mem_compositions_iff

/-- 6. On every candidate universe, `act` is an action of S3 (identity,
    composition, vertices onto vertices) that permutes the literals naturally
    and fixes the three palette anchors, as Definition 1 requires. It is a
    mathlib `MulAction` of the group `S3`, and every edge orbit has size 1, 2,
    3 or 6 (orbit-stabilizer). So `SymCandidate` is invariance under a genuine
    S3 action. -/
theorem candidate_action_is_s3_action (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) :
    (∀ v ∈ (threeColoring.attach parts).1.vertices,
        (threeColoring.attach parts).1.act (0, 1, 2) v = v) ∧
    (∀ s ∈ perms, ∀ t ∈ perms, ∀ v,
        (threeColoring.attach parts).1.act s ((threeColoring.attach parts).1.act t v)
          = (threeColoring.attach parts).1.act (compose s t) v) ∧
    (∀ s ∈ perms, ∀ v ∈ (threeColoring.attach parts).1.vertices,
        (threeColoring.attach parts).1.act s v ∈ (threeColoring.attach parts).1.vertices) ∧
    (∀ s ∈ perms, ∀ i, (threeColoring.attach parts).1.act s (.lit i) = .lit (app s i)) ∧
    (∀ s ∈ perms, ∀ a ∈ anchorsOf parts.length (threeColoring.attach parts).1,
        (threeColoring.attach parts).1.act s a = a) ∧
    Nonempty (MulAction S3
      (LegalUniverse.Vert ⟨(threeColoring.attach parts).1, attach_legal parts hparts⟩)) ∧
    (∀ e ∈ (threeColoring.attach parts).1.edges,
        ((threeColoring.attach parts).1.edgeOrbit e).length ∈ [1, 2, 3, 6]) :=
  let h := Meaning.attach_action parts hparts
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, Meaning.attach_mulAction parts hparts,
    fun _ he => Meaning.attach_edgeOrbit_length parts hparts he⟩

/-- 7. The judge: `gadgetK` returns `some b` exactly when `b = 1` and, for
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

-- The axioms each statement rests on. `lake build` prints them.
#print axioms Atlas.Statement.trident_is_symmetric_candidate
#print axioms Atlas.Statement.trident_is_valid
#print axioms Atlas.Statement.no_valid_symmetric_gadget_below_six_auxiliary_vertices
#print axioms Atlas.Statement.valid_symmetric_gadget_up_to_six_auxiliary_vertices_is_trident
#print axioms Atlas.Statement.compositions_are_all_orbit_compositions
#print axioms Atlas.Statement.candidate_action_is_s3_action
#print axioms Atlas.Statement.gadgetK_is_validity
