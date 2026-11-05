import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import atlas.ProofsAction
import atlas.ProofsLib
/-!
  P4 stage 4: the mathlib dividend.

  `perms` with `compose` is packaged as a mathlib `Group` (S3), the
  universe action as a `MulAction` on the vertex and normalized-edge
  carriers, and the orbit-stabilizer theorem
  (`MulAction.orbitProdStabilizerEquivGroup`) is applied to the engine:
  the length of every `edgeOrbit` divides |S3| = 6, so every switch the
  orbit generator can emit has size 1, 2, 3 or 6 -- exactly the sizes
  `legalSizes` hard-codes. The group and action laws were discharged in
  P4-1 (`ProofsAction`); this file only packages them into mathlib's
  algebra hierarchy and harvests the cardinality theorem.
-/

namespace Atlas

instance : DecidableEq Vertex := fun a b =>
  decidable_of_iff ((a == b) = true) beq_iff_eq

-- ------------------------------------------------------- S3 as a Group

/-- The symmetric group on the three literals, as the subtype of the
    engine's permutation table. -/
abbrev S3 : Type := {s : Perm // s ∈ perms}

instance : Mul S3 := ⟨fun a b => ⟨compose a.1 b.1, compose_mem a.1 a.2 b.1 b.2⟩⟩
instance : One S3 := ⟨⟨(0, 1, 2), id_mem_perms⟩⟩
instance : Inv S3 := ⟨fun a => ⟨pinv a.1, (pinv_spec a.1 a.2).1⟩⟩

instance : Group S3 where
  mul_assoc a b c := Subtype.ext (compose_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (id_compose a.1 a.2)
  mul_one a := Subtype.ext (compose_id a.1)
  inv_mul_cancel a := Subtype.ext ((pinv_spec a.1 a.2).2.1)

instance : Fintype S3 :=
  Fintype.ofList
    [⟨(0, 1, 2), by decide⟩, ⟨(0, 2, 1), by decide⟩, ⟨(1, 0, 2), by decide⟩,
     ⟨(1, 2, 0), by decide⟩, ⟨(2, 0, 1), by decide⟩, ⟨(2, 1, 0), by decide⟩]
    fun ⟨s, hs⟩ => by
      simp only [perms, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_self ..))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

theorem card_S3 : Nat.card S3 = 6 := by
  rw [Nat.card_eq_fintype_card]
  rfl

-- ---------------------------------------- the universe as a MulAction

/-- A universe bundled with its legality certificate -- the carrier of
    the mathlib action instances (the action laws need `legal`). -/
structure LegalUniverse where
  U : Universe
  legal : U.legal

/-- The vertex list of a legal universe, as a type. -/
def LegalUniverse.Vert (L : LegalUniverse) : Type :=
  {v : Vertex // v ∈ L.U.vertices}

instance (L : LegalUniverse) : MulAction S3 L.Vert where
  smul s v := ⟨L.U.act s.1 v.1, act_mem L.legal s.2 v.2⟩
  one_smul v := Subtype.ext (act_id L.legal v.2)
  mul_smul s t v := Subtype.ext (act_compose L.U s.2 t.2 v.1).symm

/-- The normalized edges over the universe's vertices, as a type. -/
def LegalUniverse.NEdge (L : LegalUniverse) : Type :=
  {e : Edge // e.1 ∈ L.U.vertices ∧ e.2 ∈ L.U.vertices ∧ normEdge e = e}

theorem actEdge_props {U : Universe} (hU : U.legal) {s : Perm}
    (hs : s ∈ perms) {e : Edge} (h1 : e.1 ∈ U.vertices)
    (h2 : e.2 ∈ U.vertices) :
    (U.actEdge s e).1 ∈ U.vertices ∧ (U.actEdge s e).2 ∈ U.vertices ∧
      normEdge (U.actEdge s e) = U.actEdge s e := by
  have hm1 : U.act s e.1 ∈ U.vertices := act_mem hU hs h1
  have hm2 : U.act s e.2 ∈ U.vertices := act_mem hU hs h2
  unfold Universe.actEdge
  refine ⟨?_, ?_, normEdge_idem _⟩
  · unfold normEdge
    dsimp only
    split
    · exact hm1
    · exact hm2
  · unfold normEdge
    dsimp only
    split
    · exact hm2
    · exact hm1

instance (L : LegalUniverse) : MulAction S3 L.NEdge where
  smul s e := ⟨L.U.actEdge s.1 e.1, actEdge_props L.legal s.2 e.2.1 e.2.2.1⟩
  one_smul e := Subtype.ext (actEdge_id L.legal e.2.1 e.2.2.1 e.2.2.2)
  mul_smul s t e :=
    Subtype.ext (actEdge_compose L.legal s.2 t.2 e.2.1 e.2.2.1).symm

-- ------------------------- the engine's edgeOrbit enumerates the orbit

theorem edgeOrbit_nodup (U : Universe) (e : Edge) : (U.edgeOrbit e).Nodup := by
  unfold Universe.edgeOrbit
  exact nodup_eraseDups _

/-- The engine's `edgeOrbit` list enumerates the mathlib orbit. -/
noncomputable def edgeOrbitEquiv (L : LegalUniverse) (e : L.NEdge) :
    MulAction.orbit S3 e ≃ ((L.U.edgeOrbit e.1).toFinset : Finset Edge) := by
  refine Equiv.ofBijective (fun x => ⟨x.1.1, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := x.2
    refine List.mem_toFinset.mpr (mem_edgeOrbit_iff.mpr ⟨s.1, s.2, ?_⟩)
    exact congrArg Subtype.val hs
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, hact⟩ := mem_edgeOrbit_iff.mp (List.mem_toFinset.mp hx)
    refine ⟨⟨(⟨s, hs⟩ : S3) • e, MulAction.mem_orbit e (⟨s, hs⟩ : S3)⟩, ?_⟩
    exact Subtype.ext hact

theorem card_edgeOrbit (L : LegalUniverse) (e : L.NEdge) :
    Nat.card (MulAction.orbit S3 e) = (L.U.edgeOrbit e.1).length := by
  rw [Nat.card_congr (edgeOrbitEquiv L e), Nat.card_eq_fintype_card,
    Fintype.card_coe]
  exact List.toFinset_card_of_nodup (edgeOrbit_nodup L.U e.1)

/-- Orbit-stabilizer, applied to the engine: the length of every edge
    orbit divides |S3| = 6. -/
theorem edgeOrbit_length_dvd (L : LegalUniverse) (e : L.NEdge) :
    (L.U.edgeOrbit e.1).length ∣ 6 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S3 e)
  rw [Nat.card_prod, card_S3, card_edgeOrbit] at h
  exact ⟨Nat.card (MulAction.stabilizer S3 e), h.symm⟩

/-- The P4-4 headline: every switch the orbit generator can emit has one
    of the sizes `legalSizes` hard-codes -- every edge orbit of a legal
    universe has size 1, 2, 3 or 6, by orbit-stabilizer.
    [opus5.5 review] was "are exactly": the statement is membership; that
    every size occurs is not claimed. -/
theorem edgeOrbit_length_legal {U : Universe} (hU : U.legal) {e : Edge}
    (he : e ∈ U.edges) :
    (U.edgeOrbit e).length ∈ legalSizes [1, 2, 3, 6] := by
  obtain ⟨h1, h2, hn⟩ := mem_edges he
  have hdvd : (U.edgeOrbit e).length ∣ 6 :=
    edgeOrbit_length_dvd ⟨U, hU⟩ ⟨e, h1, h2, hn⟩
  have hpos : 0 < (U.edgeOrbit e).length :=
    List.length_pos_of_mem (edgeOrbit_self hU he)
  have hle : (U.edgeOrbit e).length ≤ 6 := Nat.le_of_dvd (by omega) hdvd
  have hls : legalSizes [1, 2, 3, 6] = [1, 2, 3, 6] := rfl
  rw [hls]
  set n := (U.edgeOrbit e).length with hn'
  interval_cases n <;> first | decide | omega

end Atlas
