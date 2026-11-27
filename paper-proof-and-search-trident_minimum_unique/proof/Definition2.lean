import proof.Lemma6

/-!
  # Definition 2 (fiber) and Claim 1 (each fiber has two vertices)

  For a free orbit whose vertices each have exactly one literal neighbor,
  the fiber of a literal `x_i` is the set of vertices of the orbit adjacent
  to `x_i`. Each fiber contains exactly two vertices.

  The paper uses fibers to describe a free orbit; the proof of Theorem 16
  in `Theorem16.lean` does not need them. The count is obtained here from
  the two permutations that move the index of the literal neighbor of the
  base vertex to `i`.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable (g : Gadget V)

/-- Definition 2. The fiber of the literal `x_i` in the orbit of `v`: the
    vertices of the orbit adjacent to `x_i`. -/
def fiber (v : V) (i : Fin 3) : Set V :=
  {w | (∃ σ, g.ρ σ v = w) ∧ g.G.Adj w (g.lit i)}

/-- Claim 1. In a free orbit whose vertices have exactly one literal
    neighbor, each fiber contains exactly two vertices. -/
theorem fiber_card {v : V} (hfree : ∀ σ, g.ρ σ v = v ↔ σ = 1) {k : Fin 3}
    (hone : ∀ j, g.G.Adj v (g.lit j) ↔ j = k) (i : Fin 3) : Nat.card (g.fiber v i) = 2 := by
  -- the vertex `g.ρ σ v` is adjacent to `x_j` exactly when `j = σ k`
  have hlit : ∀ (σ : Equiv.Perm (Fin 3)) (j : Fin 3),
      g.G.Adj (g.ρ σ v) (g.lit j) ↔ j = σ k := by
    intro σ j
    have e2 : g.ρ σ⁻¹ (g.lit j) = g.lit (σ⁻¹ j) := g.ρ_lit σ⁻¹ j
    have h1 := g.adj_ρ σ⁻¹ (u := g.ρ σ v) (v := g.lit j)
    rw [g.ρ_inv_ρ, e2, hone] at h1
    rw [← h1]
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp
  -- the fiber of `x_i` corresponds to the permutations with `σ k = i`
  have e1 : {σ : Equiv.Perm (Fin 3) // σ k = i} ≃ g.fiber v i :=
    Equiv.ofBijective
      (fun σ => ⟨g.ρ σ.1 v, ⟨σ.1, rfl⟩, (hlit σ.1 i).mpr σ.2.symm⟩)
      ⟨by
        intro σ τ h
        have h1 : g.ρ σ.1 v = g.ρ τ.1 v := congrArg Subtype.val h
        rw [g.ρ_eq_ρ_iff, hfree] at h1
        exact Subtype.ext (inv_mul_eq_one.mp h1).symm,
       by
        rintro ⟨w, ⟨σ, rfl⟩, hw⟩
        exact ⟨⟨σ, ((hlit σ i).mp hw).symm⟩, rfl⟩⟩
  -- and these to the stabilizer of `k`, which has two elements
  have e2 : {σ : Equiv.Perm (Fin 3) // σ k = i} ≃
      MulAction.stabilizer (Equiv.Perm (Fin 3)) k :=
    { toFun := fun σ => ⟨(Equiv.swap k i)⁻¹ * σ.1, by
        rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, σ.2,
          Equiv.swap_inv, Equiv.swap_apply_right]⟩
      invFun := fun s => ⟨Equiv.swap k i * s.1, by
        have hs : s.1 k = k := MulAction.mem_stabilizer_iff.mp s.2
        rw [Equiv.Perm.mul_apply, hs, Equiv.swap_apply_left]⟩
      left_inv := fun σ => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  rw [← Nat.card_congr e1, Nat.card_congr e2]
  exact card_stabilizer_index k

end Gadget

end Def1

-- The build fails if this result depends on an axiom other than the three
-- standard ones.
/--
info: 'Def1.Gadget.fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.Gadget.fiber_card
