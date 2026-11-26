import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Order.Group.End
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sum

/-!
  # Definition 1 of the paper, in Mathlib terms

  This file states the paper's Definition 1 (an S3-symmetric clause gadget
  for 3-coloring and its validity) and the trident graph, using only
  Mathlib's simple graphs and permutation groups. It does not import the
  search engine. `Theorem16.lean` states the results about these
  definitions.
-/

namespace Def1

/-- Definition 1. An S3-symmetric clause gadget on the vertex type `V`: a
    simple graph with three pairwise non-adjacent literal vertices
    `lit 0`, `lit 1`, `lit 2`, a palette triangle `gT`, `gF`, `gB` with `gB`
    adjacent to every literal, and a group homomorphism `ρ` from S3 (the
    permutations of `Fin 3`) to the automorphisms of the graph that permutes
    the literals naturally and fixes each anchor. Every other vertex is an
    auxiliary vertex. -/
structure Gadget (V : Type) where
  G : SimpleGraph V
  lit : Fin 3 → V
  gT : V
  gF : V
  gB : V
  lit_inj : Function.Injective lit
  lit_ne_anchor : ∀ i, lit i ≠ gT ∧ lit i ≠ gF ∧ lit i ≠ gB
  lit_nonadj : ∀ i j, ¬ G.Adj (lit i) (lit j)
  palette : G.Adj gT gF ∧ G.Adj gF gB ∧ G.Adj gB gT
  fan : ∀ i, G.Adj gB (lit i)
  ρ : Equiv.Perm (Fin 3) →* (G ≃g G)
  ρ_lit : ∀ σ i, ρ σ (lit i) = lit (σ i)
  ρ_anchor : ∀ σ, ρ σ gT = gT ∧ ρ σ gF = gF ∧ ρ σ gB = gB

variable {V : Type}

/-- The literal coloring `α` (`true` = T, `false` = F) extends to a proper
    3-coloring with the anchors colored T, F, B. Colors: 0 = T, 1 = F,
    2 = B. -/
def Gadget.Extends (g : Gadget V) (α : Fin 3 → Bool) : Prop :=
  ∃ c : V → Fin 3, (∀ u v, g.G.Adj u v → c u ≠ c v) ∧
    c g.gT = 0 ∧ c g.gF = 1 ∧ c g.gB = 2 ∧
    ∀ i, c (g.lit i) = if α i then 0 else 1

/-- Valid: a proper extension exists exactly for the literal colorings that
    satisfy the clause `x0 ∨ x1 ∨ x2`. -/
def Gadget.Valid (g : Gadget V) : Prop :=
  ∀ α : Fin 3 → Bool, g.Extends α ↔ ∃ i, α i = true

-- ------------------------------------------------------------ the trident

/-- The twelve vertices of the trident: the literals `x i`, the branch
    vertices `p i`, the upper triangle `u i`, and the three anchors. -/
inductive TV
  | x (i : Fin 3)
  | p (i : Fin 3)
  | u (i : Fin 3)
  | gT
  | gF
  | gB
  deriving DecidableEq, Fintype

/-- The edges of the trident (Fig. 2(c) of the paper), each in one
    direction: `x i – p i`, `p i – u i`, `p i – gT`, the triangle on the
    `u i`, `x i – gB`, and the palette triangle. -/
def tridentEdge : TV → TV → Prop
  | .x i, .p j => i = j
  | .p i, .u j => i = j
  | .p _, .gT => True
  | .u i, .u j => i ≠ j
  | .x _, .gB => True
  | .gT, .gF => True
  | .gF, .gB => True
  | .gB, .gT => True
  | _, _ => False

/-- The trident graph. -/
def trident : SimpleGraph TV := SimpleGraph.fromRel tridentEdge

end Def1
