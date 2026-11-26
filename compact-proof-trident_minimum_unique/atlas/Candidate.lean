import atlas.Definition1
import atlas.OrbitLabels
import atlas.Statement
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.SetTheory.Cardinal.Finite

/-!
  From a gadget of Definition 1 to a candidate of the search engine.

  Let `g` be an S3-symmetric clause gadget on a finite vertex type `V`
  (`Definition1.lean`). The group S3 acts on the auxiliary vertices of `g`.
  By Lemma 6 (`OrbitStructure.lean`, `OrbitLabels.lean`) every orbit has size
  1, 2, 3 or 6 and can be labeled so that the action is the engine's formula
  for a part of that size. Listing the orbits in non-decreasing order of size
  gives an orbit composition `g.parts`, and sending each vertex to its label
  gives a map `g.toVertex` from `V` to the engine's vertices. The map is
  injective, lands in the candidate universe, and turns the action `g.ρ`
  into the engine's action `Universe.act`.
-/

namespace Def1

open Atlas MulAction

variable {V : Type}

namespace Gadget

variable (g : Gadget V)

-- --------------------------------------------- the action on the auxiliaries

/-- An auxiliary vertex: not a literal and not an anchor. -/
def IsAux (v : V) : Prop :=
  (∀ i, v ≠ g.lit i) ∧ v ≠ g.gT ∧ v ≠ g.gF ∧ v ≠ g.gB

/-- The auxiliary vertices. -/
abbrev Aux : Type := {v : V // g.IsAux v}

theorem gT_ne_gF : g.gT ≠ g.gF := g.palette.1.ne
theorem gF_ne_gB : g.gF ≠ g.gB := g.palette.2.1.ne
theorem gB_ne_gT : g.gB ≠ g.gT := g.palette.2.2.ne

/-- The automorphisms `g.ρ σ` map auxiliary vertices to auxiliary vertices. -/
theorem isAux_map (σ : Equiv.Perm (Fin 3)) {v : V} (h : g.IsAux v) :
    g.IsAux (g.ρ σ v) := by
  refine ⟨fun i hi => ?_, fun hT => ?_, fun hF => ?_, fun hB => ?_⟩
  · have h1 : g.ρ σ v = g.ρ σ (g.lit (σ⁻¹ i)) := by
      rw [hi, g.ρ_lit]
      simp
    exact h.1 _ ((g.ρ σ).injective h1)
  · exact h.2.1 ((g.ρ σ).injective (hT.trans (g.ρ_anchor σ).1.symm))
  · exact h.2.2.1 ((g.ρ σ).injective (hF.trans (g.ρ_anchor σ).2.1.symm))
  · exact h.2.2.2 ((g.ρ σ).injective (hB.trans (g.ρ_anchor σ).2.2.symm))

/-- S3 acts on the auxiliary vertices through `g.ρ`. -/
instance auxAction : MulAction (Equiv.Perm (Fin 3)) g.Aux where
  smul σ a := ⟨g.ρ σ a.1, g.isAux_map σ a.2⟩
  one_smul a := Subtype.ext (by
    show g.ρ 1 a.1 = a.1
    rw [map_one]
    rfl)
  mul_smul σ τ a := Subtype.ext (by
    show g.ρ (σ * τ) a.1 = g.ρ σ (g.ρ τ a.1)
    rw [map_mul]
    rfl)

/-- Every vertex is a literal, an anchor, or an auxiliary vertex. -/
theorem vertex_cases (v : V) :
    (∃ i, v = g.lit i) ∨ v = g.gT ∨ v = g.gF ∨ v = g.gB ∨ ∃ a : g.Aux, v = a.1 := by
  by_cases h1 : ∃ i, v = g.lit i
  · exact Or.inl h1
  by_cases h2 : v = g.gT
  · exact Or.inr (Or.inl h2)
  by_cases h3 : v = g.gF
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : v = g.gB
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨v, fun i hi => h1 ⟨i, hi⟩, h2, h3, h4⟩, rfl⟩)))

-- ------------------------------------------------- the orbits and their labels

/-- The orbits of auxiliary vertices. -/
abbrev Orb : Type := orbitRel.Quotient (Equiv.Perm (Fin 3)) g.Aux

theorem mem_orbit_out {a : g.Aux} {ω : g.Orb} :
    a ∈ orbit (Equiv.Perm (Fin 3)) ω.out ↔ (Quotient.mk'' a : g.Orb) = ω := by
  rw [← orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq',
    orbitRel.Quotient.mem_orbit]

theorem mk_smul (σ : Equiv.Perm (Fin 3)) (a : g.Aux) :
    (Quotient.mk'' (σ • a) : g.Orb) = Quotient.mk'' a :=
  orbitRel.Quotient.quotient_smul_eq

/-- Lemma 6 for the orbit `ω`: its size and a labeling with the engine's
    action. -/
theorem orb_data (ω : g.Orb) :
    ∃ n, (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) ∧
      Nat.card (orbit (Equiv.Perm (Fin 3)) ω.out) = n ∧
      ∃ lab : g.Aux → Nat,
        (∀ x ∈ orbit (Equiv.Perm (Fin 3)) ω.out, lab x < n) ∧
        (∀ x ∈ orbit (Equiv.Perm (Fin 3)) ω.out,
          ∀ y ∈ orbit (Equiv.Perm (Fin 3)) ω.out, lab x = lab y → x = y) ∧
        (∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ orbit (Equiv.Perm (Fin 3)) ω.out,
          lab (σ • x) = stdAct n (toTable σ) (lab x)) :=
  exists_engine_labeling ω.out

/-- The size of an orbit. -/
noncomputable def osize (ω : g.Orb) : Nat := Classical.choose (g.orb_data ω)

theorem osize_legal (ω : g.Orb) :
    g.osize ω = 1 ∨ g.osize ω = 2 ∨ g.osize ω = 3 ∨ g.osize ω = 6 :=
  (Classical.choose_spec (g.orb_data ω)).1

theorem osize_card (ω : g.Orb) :
    Nat.card (orbit (Equiv.Perm (Fin 3)) ω.out) = g.osize ω :=
  (Classical.choose_spec (g.orb_data ω)).2.1

/-- The labeling of an orbit. -/
noncomputable def olab (ω : g.Orb) : g.Aux → Nat :=
  Classical.choose (Classical.choose_spec (g.orb_data ω)).2.2

theorem olab_spec (ω : g.Orb) :
    (∀ x ∈ orbit (Equiv.Perm (Fin 3)) ω.out, g.olab ω x < g.osize ω) ∧
    (∀ x ∈ orbit (Equiv.Perm (Fin 3)) ω.out,
      ∀ y ∈ orbit (Equiv.Perm (Fin 3)) ω.out, g.olab ω x = g.olab ω y → x = y) ∧
    (∀ σ : Equiv.Perm (Fin 3), ∀ x ∈ orbit (Equiv.Perm (Fin 3)) ω.out,
      g.olab ω (σ • x) = stdAct (g.osize ω) (toTable σ) (g.olab ω x)) :=
  Classical.choose_spec (Classical.choose_spec (g.orb_data ω)).2.2

/-- The label of an auxiliary vertex inside its orbit. -/
noncomputable def alab (a : g.Aux) : Nat := g.olab (Quotient.mk'' a) a

theorem alab_lt (a : g.Aux) : g.alab a < g.osize (Quotient.mk'' a) :=
  (g.olab_spec _).1 a (g.mem_orbit_out.mpr rfl)

theorem alab_inj {a b : g.Aux} (h : (Quotient.mk'' a : g.Orb) = Quotient.mk'' b)
    (hl : g.alab a = g.alab b) : a = b := by
  unfold alab at hl
  rw [← h] at hl
  exact (g.olab_spec _).2.1 a (g.mem_orbit_out.mpr rfl) b (g.mem_orbit_out.mpr h.symm) hl

theorem alab_smul (σ : Equiv.Perm (Fin 3)) (a : g.Aux) :
    g.alab (σ • a) = stdAct (g.osize (Quotient.mk'' a)) (toTable σ) (g.alab a) := by
  unfold alab
  rw [g.mk_smul σ a]
  exact (g.olab_spec _).2.2 σ a (g.mem_orbit_out.mpr rfl)

-- ------------------------------------------- the orbits in order of size

variable [Finite V]

/-- The number of auxiliary orbits. -/
noncomputable def m : Nat := Nat.card g.Orb

/-- The orbit at position `i`, in non-decreasing order of size. -/
noncomputable def orbAt : Fin g.m ≃ g.Orb :=
  (Tuple.sort fun i => g.osize ((Finite.equivFin g.Orb).symm i)).trans
    (Finite.equivFin g.Orb).symm

theorem osize_orbAt_mono : Monotone fun i => g.osize (g.orbAt i) :=
  Tuple.monotone_sort fun i => g.osize ((Finite.equivFin g.Orb).symm i)

/-- The position of an orbit. -/
noncomputable def pos (ω : g.Orb) : Fin g.m := g.orbAt.symm ω

theorem orbAt_pos (ω : g.Orb) : g.orbAt (g.pos ω) = ω := g.orbAt.apply_symm_apply ω

theorem pos_injective : Function.Injective g.pos := g.orbAt.symm.injective

/-- The orbit composition of the gadget: the sizes of its auxiliary orbits
    in non-decreasing order. -/
noncomputable def parts : List Nat := List.ofFn fun i => g.osize (g.orbAt i)

theorem parts_length : g.parts.length = g.m := List.length_ofFn

theorem parts_getD (ω : g.Orb) : g.parts.getD (g.pos ω).val 0 = g.osize ω := by
  have hlt : (g.pos ω).val < (List.ofFn fun i => g.osize (g.orbAt i)).length := by
    rw [List.length_ofFn]
    exact (g.pos ω).isLt
  show (List.ofFn fun i => g.osize (g.orbAt i)).getD (g.pos ω).val 0 = g.osize ω
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
  exact congrArg g.osize (g.orbAt_pos ω)

theorem parts_legal : ∀ n ∈ g.parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  unfold parts
  rw [List.forall_mem_ofFn_iff]
  intro i
  exact g.osize_legal _

theorem parts_sorted : g.parts.Pairwise (· ≤ ·) := by
  unfold parts
  rw [List.pairwise_ofFn]
  intro i j hij
  exact g.osize_orbAt_mono hij.le

/-- The sizes of the orbits add up to the number of auxiliary vertices. -/
theorem parts_sum : g.parts.sum = Nat.card g.Aux := by
  have : Fintype g.Orb := Fintype.ofFinite _
  unfold parts
  rw [List.sum_ofFn, Fintype.sum_equiv g.orbAt (fun i => g.osize (g.orbAt i)) g.osize
    (fun _ => rfl), Nat.card_congr (selfEquivSigmaOrbits (Equiv.Perm (Fin 3)) g.Aux),
    Nat.card_sigma]
  exact Finset.sum_congr rfl fun ω _ => (g.osize_card ω).symm

-- ------------------------------------------------------- the vertex map

/-- The candidate universe of the gadget. -/
noncomputable def U : Universe := (threeColoring.attach g.parts).1

theorem U_legal : g.U.legal := attach_legal g.parts g.parts_legal

theorem U_parts_length : g.U.parts.length = g.m + 3 := by
  show (g.parts ++ [1, 1, 1]).length = g.m + 3
  rw [List.length_append, parts_length]
  rfl

theorem pos_lt (ω : g.Orb) : (g.pos ω).val < g.m := (g.pos ω).isLt

theorem U_size_pos (ω : g.Orb) : g.U.size (g.pos ω).val = g.osize ω := by
  show (g.parts ++ [1, 1, 1]).getD (g.pos ω).val 0 = g.osize ω
  rw [List.getD_append _ _ _ _ (by rw [parts_length]; exact g.pos_lt ω)]
  exact g.parts_getD ω

theorem U_size_anchor {d : Nat} (hd : d < 3) : g.U.size (g.m + d) = 1 := by
  have h := attach_size g.parts hd
  rwa [parts_length] at h

open Classical in
/-- The engine vertex of a vertex of the gadget: literal `i` goes to
    `.lit i`, an auxiliary vertex to its orbit's position and its label, and
    the anchors to the three parts after the auxiliary orbits. -/
noncomputable def toVertex (v : V) : Vertex :=
  if h : ∃ i, g.lit i = v then .lit (Classical.choose h).val
  else if v = g.gT then .aux g.m 0
  else if v = g.gF then .aux (g.m + 1) 0
  else if v = g.gB then .aux (g.m + 2) 0
  else if h' : g.IsAux v then
    .aux (g.pos (Quotient.mk'' ⟨v, h'⟩)).val (g.alab ⟨v, h'⟩)
  else .lit 0

theorem toVertex_lit (i : Fin 3) : g.toVertex (g.lit i) = .lit i.val := by
  have h : ∃ j, g.lit j = g.lit i := ⟨i, rfl⟩
  unfold toVertex
  rw [dif_pos h, g.lit_inj (Classical.choose_spec h)]

theorem toVertex_gT : g.toVertex g.gT = .aux g.m 0 := by
  have h : ¬ ∃ j, g.lit j = g.gT := fun ⟨j, hj⟩ => (g.lit_ne_anchor j).1 hj
  unfold toVertex
  rw [dif_neg h, if_pos rfl]

theorem toVertex_gF : g.toVertex g.gF = .aux (g.m + 1) 0 := by
  have h : ¬ ∃ j, g.lit j = g.gF := fun ⟨j, hj⟩ => (g.lit_ne_anchor j).2.1 hj
  unfold toVertex
  rw [dif_neg h, if_neg g.gT_ne_gF.symm, if_pos rfl]

theorem toVertex_gB : g.toVertex g.gB = .aux (g.m + 2) 0 := by
  have h : ¬ ∃ j, g.lit j = g.gB := fun ⟨j, hj⟩ => (g.lit_ne_anchor j).2.2 hj
  unfold toVertex
  rw [dif_neg h, if_neg g.gB_ne_gT, if_neg g.gF_ne_gB.symm, if_pos rfl]

theorem toVertex_aux (a : g.Aux) :
    g.toVertex a.1 = .aux (g.pos (Quotient.mk'' a)).val (g.alab a) := by
  obtain ⟨v, hv⟩ := a
  have h : ¬ ∃ j, g.lit j = v := fun ⟨j, hj⟩ => hv.1 j hj.symm
  unfold toVertex
  rw [dif_neg h, if_neg hv.2.1, if_neg hv.2.2.1, if_neg hv.2.2.2, dif_pos hv]

/-- The image of every vertex is a vertex of the candidate universe. -/
theorem toVertex_mem (v : V) : g.toVertex v ∈ g.U.vertices := by
  have h0 : g.U.size g.m = 1 := g.U_size_anchor (d := 0) (by omega)
  have h1 : g.U.size (g.m + 1) = 1 := g.U_size_anchor (d := 1) (by omega)
  have h2 : g.U.size (g.m + 2) = 1 := g.U_size_anchor (d := 2) (by omega)
  have hlen := g.U_parts_length
  rcases g.vertex_cases v with ⟨i, rfl⟩ | rfl | rfl | rfl | ⟨a, rfl⟩
  · rw [toVertex_lit]
    exact mem_vertices.mpr (Or.inl ⟨i.val, i.isLt, rfl⟩)
  · rw [toVertex_gT]
    exact mem_vertices.mpr (Or.inr ⟨g.m, 0, by omega, by omega, rfl⟩)
  · rw [toVertex_gF]
    exact mem_vertices.mpr (Or.inr ⟨g.m + 1, 0, by omega, by omega, rfl⟩)
  · rw [toVertex_gB]
    exact mem_vertices.mpr (Or.inr ⟨g.m + 2, 0, by omega, by omega, rfl⟩)
  · rw [toVertex_aux]
    have hp := g.pos_lt (Quotient.mk'' a)
    refine mem_vertices.mpr (Or.inr ⟨_, _, by omega, ?_, rfl⟩)
    rw [U_size_pos]
    exact g.alab_lt a

/-- Only literals go to literal vertices. -/
theorem eq_lit_of_toVertex {v : V} {i : Nat} (h : g.toVertex v = .lit i) :
    ∃ j, v = g.lit j := by
  rcases g.vertex_cases v with ⟨j, rfl⟩ | rfl | rfl | rfl | ⟨a, rfl⟩
  · exact ⟨j, rfl⟩
  · rw [toVertex_gT] at h
    exact Vertex.noConfusion h
  · rw [toVertex_gF] at h
    exact Vertex.noConfusion h
  · rw [toVertex_gB] at h
    exact Vertex.noConfusion h
  · rw [toVertex_aux] at h
    exact Vertex.noConfusion h

/-- Different vertices have different images. -/
theorem toVertex_injective : Function.Injective g.toVertex := by
  intro v w h
  rcases g.vertex_cases v with ⟨i, rfl⟩ | rfl | rfl | rfl | ⟨a, rfl⟩
  · -- `v` is a literal
    rw [toVertex_lit] at h
    obtain ⟨j, rfl⟩ := g.eq_lit_of_toVertex h.symm
    rw [toVertex_lit] at h
    rw [Fin.ext (Vertex.lit.inj h)]
  · -- `v = gT`
    rw [toVertex_gT] at h
    rcases g.vertex_cases w with ⟨j, rfl⟩ | rfl | rfl | rfl | ⟨b, rfl⟩
    · rw [toVertex_lit] at h
      exact Vertex.noConfusion h
    · rfl
    · rw [toVertex_gF] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_gB] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_aux] at h
      have hp := g.pos_lt (Quotient.mk'' b)
      exact absurd (Vertex.aux.inj h).1 (by omega)
  · -- `v = gF`
    rw [toVertex_gF] at h
    rcases g.vertex_cases w with ⟨j, rfl⟩ | rfl | rfl | rfl | ⟨b, rfl⟩
    · rw [toVertex_lit] at h
      exact Vertex.noConfusion h
    · rw [toVertex_gT] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rfl
    · rw [toVertex_gB] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_aux] at h
      have hp := g.pos_lt (Quotient.mk'' b)
      exact absurd (Vertex.aux.inj h).1 (by omega)
  · -- `v = gB`
    rw [toVertex_gB] at h
    rcases g.vertex_cases w with ⟨j, rfl⟩ | rfl | rfl | rfl | ⟨b, rfl⟩
    · rw [toVertex_lit] at h
      exact Vertex.noConfusion h
    · rw [toVertex_gT] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_gF] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rfl
    · rw [toVertex_aux] at h
      have hp := g.pos_lt (Quotient.mk'' b)
      exact absurd (Vertex.aux.inj h).1 (by omega)
  · -- `v` is auxiliary
    rw [toVertex_aux] at h
    have hp := g.pos_lt (Quotient.mk'' a)
    rcases g.vertex_cases w with ⟨j, rfl⟩ | rfl | rfl | rfl | ⟨b, rfl⟩
    · rw [toVertex_lit] at h
      exact Vertex.noConfusion h
    · rw [toVertex_gT] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_gF] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_gB] at h
      exact absurd (Vertex.aux.inj h).1 (by omega)
    · rw [toVertex_aux] at h
      obtain ⟨h1, h2⟩ := Vertex.aux.inj h
      have hω : (Quotient.mk'' a : g.Orb) = Quotient.mk'' b :=
        g.pos_injective (Fin.ext h1)
      rw [g.alab_inj hω h2]

/-- The map turns the action of the gadget into the engine's action. -/
theorem toVertex_map (σ : Equiv.Perm (Fin 3)) (v : V) :
    g.toVertex (g.ρ σ v) = g.U.act (toTable σ) (g.toVertex v) := by
  rcases g.vertex_cases v with ⟨i, rfl⟩ | rfl | rfl | rfl | ⟨a, rfl⟩
  · rw [g.ρ_lit, toVertex_lit, toVertex_lit]
    show Vertex.lit (σ i).val = Vertex.lit (app (toTable σ) i.val)
    rw [app_toTable]
  · rw [(g.ρ_anchor σ).1, toVertex_gT]
    exact (act_aux_one (toTable σ) 0 (g.U_size_anchor (d := 0) (by omega))).symm
  · rw [(g.ρ_anchor σ).2.1, toVertex_gF]
    exact (act_aux_one (toTable σ) 0 (g.U_size_anchor (d := 1) (by omega))).symm
  · rw [(g.ρ_anchor σ).2.2, toVertex_gB]
    exact (act_aux_one (toTable σ) 0 (g.U_size_anchor (d := 2) (by omega))).symm
  · have h1 : g.ρ σ a.1 = (σ • a).1 := rfl
    rw [h1, toVertex_aux, toVertex_aux, act_aux_std, g.mk_smul, g.alab_smul, U_size_pos]

end Gadget

end Def1
