import Mathlib.Data.List.Nodup
import Mathlib.Tactic.IntervalCases
import atlas.Framework
/-!
  P4 stage 1: the S3 action is a group action -- and the engine facts
  the later stages read off it.

  * Finite group facts (closure, identity, inverses, the parity
    homomorphism, the value-table round trips): `decide` over the
    six-element list `perms`; the composition laws.
  * Legal parts and the vertex-membership shape: universes built by the
    atlas have part sizes in {1, 2, 3, 6} (`legalSizes`); the laws that
    read a part's size carry that hypothesis as `Universe.legal`.
  * Action laws, by case analysis over the four orbit types:
    `act_compose` for every universe; `act_id`, membership preservation
    and injectivity on the universe under `legal`.
  * Edge algebra (`normEdge` swap-invariance and idempotence, `edgeOrbit`
    containing its seed, closed and `act`-stable) and the inverse tables.
  * Vertex-list and edge-list basics (`vertices_nodup`, `edges_ne`,
    `mem_edges`) and closure of the edge list under the action when
    literal-literal edges are off (`mem_edges_of_norm`).
  * The orbit generator emits orbits (`orbits_spec`, `orbit_switch_props`)
    -- the P4-5 material behind `graphs_symmetric_props` in ProofsSym.
    Coverage (every edge lies in some emitted switch) and the converse
    "every S3-invariant graph is enumerated, up to edge set" are P4-6,
    `atlas/ProofsCover.lean`.
-/

namespace Atlas

open List

-- ------------------------------------------------------ finite group facts

theorem id_mem_perms : ((0, 1, 2) : Perm) ∈ perms := by decide

theorem compose_mem : ∀ s ∈ perms, ∀ t ∈ perms, compose s t ∈ perms := by
  decide

theorem exists_inv : ∀ s ∈ perms, ∃ t, t ∈ perms ∧
    compose t s = (0, 1, 2) ∧ compose s t = (0, 1, 2) := by decide

theorem parity_compose : ∀ s ∈ perms, ∀ t ∈ perms,
    parity (compose s t) = parity s ^^^ parity t := by decide

theorem pidx_getD : ∀ s ∈ perms, perms.getD (pidx s) (0, 1, 2) = s := by
  decide

theorem pidx_getD_lt : ∀ j, j < 6 → pidx (perms.getD j (0, 1, 2)) = j := by
  decide

theorem app_lt_three : ∀ s ∈ perms,
    app s 0 < 3 ∧ app s 1 < 3 ∧ app s 2 < 3 := by decide

theorem app_lt {s : Perm} (hs : s ∈ perms) {i : Nat} (hi : i < 3) :
    app s i < 3 := by
  obtain ⟨h0, h1, h2⟩ := app_lt_three s hs
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2

theorem getD_perms_mem (j : Nat) : perms.getD j (0, 1, 2) ∈ perms := by
  by_cases hj : j < 6
  · interval_cases j <;> decide
  · have h6 : perms.length ≤ j := by
      have : perms.length = 6 := rfl
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h6]
    exact id_mem_perms

-- --------------------------------------------------------- composition laws

theorem app_compose (s t : Perm) : ∀ i, app (compose s t) i = app s (app t i)
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem compose_assoc (s t u : Perm) :
    compose (compose s t) u = compose s (compose t u) := by
  show (app (compose s t) u.1, app (compose s t) u.2.1,
    app (compose s t) u.2.2) = _
  rw [app_compose, app_compose, app_compose]
  rfl

theorem compose_id (s : Perm) : compose s (0, 1, 2) = s := rfl

theorem id_compose : ∀ s ∈ perms, compose (0, 1, 2) s = s := by decide

-- ------------------------------------------------------------- legal parts

/-- The orbit-type sizes the atlas enumerates (`legalSizes`). -/
def Universe.legal (U : Universe) : Prop :=
  ∀ n ∈ U.parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6

theorem legal_size {U : Universe} (hU : U.legal) {p : Nat}
    (hp : p < U.parts.length) :
    U.size p = 1 ∨ U.size p = 2 ∨ U.size p = 3 ∨ U.size p = 6 := by
  refine hU (U.parts.getD p 0) ?_
  have : U.parts.getD p 0 = U.parts[p] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
    rfl
  rw [this]
  exact List.getElem_mem hp

theorem legal_size_le {U : Universe} (hU : U.legal) {p : Nat}
    (hp : p < U.parts.length) : U.size p ≤ 6 := by
  rcases legal_size hU hp with h | h | h | h <;> omega

-- ------------------------------------------------- vertex membership shape

theorem mem_vertices {U : Universe} {v : Vertex} :
    v ∈ U.vertices ↔
      (∃ i, i < 3 ∧ v = .lit i) ∨
      (∃ p j, p < U.parts.length ∧ j < U.size p ∧ v = .aux p j) := by
  unfold Universe.vertices
  rw [List.mem_append]
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      exact Or.inl ⟨i, List.mem_range.mp hi, rfl⟩
    · obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp h
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
      exact Or.inr ⟨p, j, List.mem_range.mp hp, List.mem_range.mp hj, rfl⟩
  · intro h
    rcases h with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩
    · exact Or.inl (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    · exact Or.inr (List.mem_flatMap.mpr
        ⟨p, List.mem_range.mpr hp,
         List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩)

-- ------------------------------------------------------------- action laws

/-- Size-conditioned rewrite forms of the action on auxiliary vertices. -/
theorem act_aux_one {U : Universe} {p : Nat} (s : Perm) (j : Nat)
    (h : U.size p = 1) : U.act s (.aux p j) = .aux p j := by
  unfold Universe.act
  dsimp only
  rw [h]
  rfl

theorem act_aux_two {U : Universe} {p : Nat} (s : Perm) (j : Nat)
    (h : U.size p = 2) : U.act s (.aux p j) = .aux p (j ^^^ parity s) := by
  unfold Universe.act
  dsimp only
  rw [h]
  rfl

theorem act_aux_three {U : Universe} {p : Nat} (s : Perm) (j : Nat)
    (h : U.size p = 3) : U.act s (.aux p j) = .aux p (app s j) := by
  unfold Universe.act
  dsimp only
  rw [h]
  rfl

theorem act_aux_reg {U : Universe} {p : Nat} (s : Perm) (j : Nat)
    (h : U.size p = 0 ∨ 4 ≤ U.size p) :
    U.act s (.aux p j) = .aux p (pidx (compose s (perms.getD j (0, 1, 2)))) := by
  unfold Universe.act
  dsimp only
  rcases h with h | h
  · rw [h]
    rfl
  · obtain ⟨m, hm⟩ : ∃ m, U.size p = m + 4 := ⟨U.size p - 4, by omega⟩
    rw [hm]
    rfl

theorem act_compose (U : Universe) {s t : Perm} (hs : s ∈ perms)
    (ht : t ∈ perms) (v : Vertex) :
    U.act s (U.act t v) = U.act (compose s t) v := by
  cases v with
  | lit i =>
    simp only [Universe.act, app_compose]
  | aux p j =>
    have hu : perms.getD j (0, 1, 2) ∈ perms := getD_perms_mem j
    have hcu : compose t (perms.getD j (0, 1, 2)) ∈ perms :=
      compose_mem t ht _ hu
    rcases hsize : U.size p with _ | _ | _ | _ | m
    · rw [act_aux_reg t j (Or.inl hsize), act_aux_reg s _ (Or.inl hsize),
        act_aux_reg (compose s t) j (Or.inl hsize), pidx_getD _ hcu,
        compose_assoc]
    · rw [act_aux_one t j hsize, act_aux_one s j hsize,
        act_aux_one (compose s t) j hsize]
    · rw [act_aux_two t j hsize, act_aux_two s _ hsize,
        act_aux_two (compose s t) j hsize, Nat.xor_assoc,
        Nat.xor_comm (parity t) (parity s), ← parity_compose s hs t ht]
    · rw [act_aux_three t j hsize, act_aux_three s _ hsize,
        act_aux_three (compose s t) j hsize, app_compose]
    · have h4 : 4 ≤ U.size p := by omega
      rw [act_aux_reg t j (Or.inr h4), act_aux_reg s _ (Or.inr h4),
        act_aux_reg (compose s t) j (Or.inr h4), pidx_getD _ hcu,
        compose_assoc]

theorem app_id {i : Nat} (hi : i < 3) : app (0, 1, 2) i = i := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

theorem act_id {U : Universe} (hU : U.legal) {v : Vertex}
    (hv : v ∈ U.vertices) : U.act (0, 1, 2) v = v := by
  rcases mem_vertices.mp hv with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩
  · simp only [Universe.act, app_id hi]
  · rcases legal_size hU hp with h | h | h | h
    · rw [act_aux_one _ _ h]
    · rw [act_aux_two _ _ h]
      have hpar : parity ((0,1,2) : Perm) = 0 := rfl
      rw [hpar, Nat.xor_zero]
    · rw [act_aux_three _ _ h, app_id (h ▸ hj)]
    · rw [act_aux_reg _ _ (Or.inr (by omega)),
        id_compose _ (getD_perms_mem j), pidx_getD_lt j (by omega)]

theorem act_mem {U : Universe} (hU : U.legal) {s : Perm} (hs : s ∈ perms)
    {v : Vertex} (hv : v ∈ U.vertices) : U.act s v ∈ U.vertices := by
  rcases mem_vertices.mp hv with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩
  · exact mem_vertices.mpr (Or.inl ⟨app s i, app_lt hs hi, rfl⟩)
  · refine mem_vertices.mpr (Or.inr ?_)
    rcases legal_size hU hp with h | h | h | h
    · rw [act_aux_one _ _ h]
      exact ⟨p, j, hp, hj, rfl⟩
    · rw [act_aux_two _ _ h]
      refine ⟨p, j ^^^ parity s, hp, ?_, rfl⟩
      rw [h] at hj ⊢
      have hpar : parity s = 0 ∨ parity s = 1 := by
        unfold parity
        split <;> simp
      interval_cases j <;> rcases hpar with hp2 | hp2 <;> rw [hp2] <;> decide
    · rw [act_aux_three _ _ h]
      refine ⟨p, app s j, hp, ?_, rfl⟩
      rw [h] at hj ⊢
      exact app_lt hs hj
    · rw [act_aux_reg _ _ (Or.inr (by omega))]
      refine ⟨p, _, hp, ?_, rfl⟩
      rw [h]
      have hm : compose s (perms.getD j (0,1,2)) ∈ perms :=
        compose_mem s hs _ (getD_perms_mem j)
      revert hm
      generalize compose s (perms.getD j (0,1,2)) = u
      revert u
      decide

theorem act_inj {U : Universe} (hU : U.legal) {s : Perm} (hs : s ∈ perms)
    {v w : Vertex} (hv : v ∈ U.vertices) (hw : w ∈ U.vertices)
    (h : U.act s v = U.act s w) : v = w := by
  obtain ⟨t, ht, hts, _⟩ := exists_inv s hs
  have hv' := act_compose U ht hs v
  have hw' := act_compose U ht hs w
  rw [h] at hv'
  rw [hts, act_id hU hv] at hv'
  rw [hts, act_id hU hw] at hw'
  exact hv'.symm.trans hw'

-- ----------------------------------------------------------- edge algebra

instance : LawfulBEq Vertex where
  eq_of_beq {a b} h := by
    cases a with
    | lit i =>
      cases b with
      | lit i' =>
        have h' : (i == i') = true := h
        exact congrArg Vertex.lit (eq_of_beq h')
      | aux p j => nomatch h
    | aux p j =>
      cases b with
      | lit i => nomatch h
      | aux p' j' =>
        have h' : (p == p' && j == j') = true := h
        simp only [Bool.and_eq_true, beq_iff_eq] at h'
        rw [h'.1, h'.2]
  rfl {a} := by
    cases a with
    | lit i =>
      show (i == i) = true
      simp
    | aux p j =>
      show (p == p && j == j) = true
      simp

theorem key_inj {U : Universe} (hU : U.legal) {v w : Vertex}
    (hv : v ∈ U.vertices) (hw : w ∈ U.vertices) (h : v.key = w.key) :
    v = w := by
  rcases mem_vertices.mp hv with ⟨i, hi, rfl⟩ | ⟨p, j, hp, hj, rfl⟩ <;>
    rcases mem_vertices.mp hw with ⟨i', hi', rfl⟩ | ⟨p', j', hp', hj', rfl⟩ <;>
    simp only [Vertex.key] at h
  · rw [h]
  · have := legal_size_le hU hp'
    omega
  · have := legal_size_le hU hp
    omega
  · have h6 : j < 6 := lt_of_lt_of_le hj (legal_size_le hU hp)
    have h6' : j' < 6 := lt_of_lt_of_le hj' (legal_size_le hU hp')
    have hpp : p = p' := by omega
    have hjj : j = j' := by omega
    rw [hpp, hjj]

theorem normEdge_comm {U : Universe} (hU : U.legal) {a b : Vertex}
    (ha : a ∈ U.vertices) (hb : b ∈ U.vertices) :
    normEdge (a, b) = normEdge (b, a) := by
  unfold normEdge
  by_cases hab : a.key ≤ b.key
  · by_cases hba : b.key ≤ a.key
    · have : a = b := key_inj hU ha hb (Nat.le_antisymm hab hba)
      rw [if_pos hab, if_pos hba, this]
    · rw [if_pos hab, if_neg hba]
  · by_cases hba : b.key ≤ a.key
    · rw [if_neg hab, if_pos hba]
    · omega

theorem normEdge_idem (e : Edge) : normEdge (normEdge e) = normEdge e := by
  unfold normEdge
  by_cases h : e.1.key ≤ e.2.key
  · rw [if_pos h, if_pos h]
  · rw [if_neg h]
    dsimp only
    rw [if_pos (by omega)]

theorem mem_unorderedPairs {α : Type} {l : List α} {x y : α}
    (h : (x, y) ∈ unorderedPairs l) : x ∈ l ∧ y ∈ l := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    simp only [unorderedPairs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨b, hb, heq⟩ := List.mem_map.mp h
      cases heq
      exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hb⟩
    · obtain ⟨hx, hy⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

theorem mem_edges {U : Universe} {e : Edge} (he : e ∈ U.edges) :
    e.1 ∈ U.vertices ∧ e.2 ∈ U.vertices ∧ normEdge e = e := by
  unfold Universe.edges at he
  obtain ⟨⟨a, b⟩, hab, harm⟩ := List.mem_filterMap.mp he
  obtain ⟨hav, hbv⟩ := mem_unorderedPairs hab
  have hnorm : e = normEdge (a, b) := by
    revert harm
    split
    · split
      · intro h
        exact (Option.some.inj h).symm
      · intro h
        cases h
    · intro h
      exact (Option.some.inj h).symm
  have hends : (normEdge (a, b)).1 ∈ U.vertices ∧
      (normEdge (a, b)).2 ∈ U.vertices := by
    unfold normEdge
    dsimp only
    split
    · exact ⟨hav, hbv⟩
    · exact ⟨hbv, hav⟩
  refine ⟨hnorm ▸ hends.1, hnorm ▸ hends.2, ?_⟩
  rw [hnorm, normEdge_idem]

theorem actEdge_compose {U : Universe} (hU : U.legal) {s t : Perm}
    (hs : s ∈ perms) (ht : t ∈ perms) {e : Edge}
    (h1 : e.1 ∈ U.vertices) (h2 : e.2 ∈ U.vertices) :
    U.actEdge s (U.actEdge t e) = U.actEdge (compose s t) e := by
  unfold Universe.actEdge
  have m1 : U.act t e.1 ∈ U.vertices := act_mem hU ht h1
  have m2 : U.act t e.2 ∈ U.vertices := act_mem hU ht h2
  unfold normEdge
  dsimp only
  by_cases h : (U.act t e.1).key ≤ (U.act t e.2).key
  · rw [if_pos h]
    dsimp only
    rw [act_compose U hs ht, act_compose U hs ht]
  · rw [if_neg h]
    dsimp only
    have : normEdge (U.act s (U.act t e.2), U.act s (U.act t e.1))
        = normEdge (U.act s (U.act t e.1), U.act s (U.act t e.2)) :=
      normEdge_comm hU (act_mem hU hs m2) (act_mem hU hs m1)
    unfold normEdge at this
    dsimp only at this
    rw [this, act_compose U hs ht, act_compose U hs ht]

theorem actEdge_id {U : Universe} (hU : U.legal) {e : Edge}
    (h1 : e.1 ∈ U.vertices) (h2 : e.2 ∈ U.vertices) (hn : normEdge e = e) :
    U.actEdge (0, 1, 2) e = e := by
  unfold Universe.actEdge
  rw [act_id hU h1, act_id hU h2]
  exact hn

theorem mem_edgeOrbit_iff {U : Universe} {e e' : Edge} :
    e' ∈ U.edgeOrbit e ↔ ∃ s ∈ perms, U.actEdge s e = e' := by
  unfold Universe.edgeOrbit
  rw [List.mem_eraseDups, List.mem_map]

theorem edgeOrbit_self {U : Universe} (hU : U.legal) {e : Edge}
    (he : e ∈ U.edges) : e ∈ U.edgeOrbit e := by
  obtain ⟨h1, h2, hn⟩ := mem_edges he
  exact mem_edgeOrbit_iff.mpr ⟨(0, 1, 2), id_mem_perms, actEdge_id hU h1 h2 hn⟩

theorem edgeOrbit_closed {U : Universe} (hU : U.legal) {s : Perm}
    (hs : s ∈ perms) {e e' : Edge} (h1 : e.1 ∈ U.vertices)
    (h2 : e.2 ∈ U.vertices) (h : e' ∈ U.edgeOrbit e) :
    U.actEdge s e' ∈ U.edgeOrbit e := by
  obtain ⟨t, ht, rfl⟩ := mem_edgeOrbit_iff.mp h
  exact mem_edgeOrbit_iff.mpr
    ⟨compose s t, compose_mem s hs t ht,
     (actEdge_compose hU hs ht h1 h2).symm⟩

theorem edgeOrbit_subset {U : Universe} (hU : U.legal) {e e' : Edge}
    (h1 : e.1 ∈ U.vertices) (h2 : e.2 ∈ U.vertices)
    (h : e' ∈ U.edgeOrbit e) : U.edgeOrbit e' ⊆ U.edgeOrbit e := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := mem_edgeOrbit_iff.mp h
  obtain ⟨u, hu, rfl⟩ := mem_edgeOrbit_iff.mp hx
  exact mem_edgeOrbit_iff.mpr
    ⟨compose u t, compose_mem u hu t ht,
     (actEdge_compose hU hu ht h1 h2).symm⟩

theorem edgeOrbit_symm {U : Universe} (hU : U.legal) {e e' : Edge}
    (he : e ∈ U.edges) (h : e' ∈ U.edgeOrbit e) : e ∈ U.edgeOrbit e' := by
  obtain ⟨h1, h2, hn⟩ := mem_edges he
  obtain ⟨t, ht, rfl⟩ := mem_edgeOrbit_iff.mp h
  obtain ⟨u, hu, hut, _⟩ := exists_inv t ht
  refine mem_edgeOrbit_iff.mpr ⟨u, hu, ?_⟩
  rw [actEdge_compose hU hu ht h1 h2, hut, actEdge_id hU h1 h2 hn]

-- ---------------------------------------------------------- inverse tables

/-- The inverse permutation, read off the group table. -/
def pinv (s : Perm) : Perm :=
  (perms.find? fun t => compose t s == (0, 1, 2)).getD (0, 1, 2)

theorem pinv_spec : ∀ s ∈ perms, pinv s ∈ perms ∧
    compose (pinv s) s = (0, 1, 2) ∧ compose s (pinv s) = (0, 1, 2) := by
  decide

/-- Acting by `s` and then by its inverse is the identity on the universe. -/
theorem act_pinv_act {U : Universe} (hU : U.legal) {s : Perm} (hs : s ∈ perms)
    {v : Vertex} (hv : v ∈ U.vertices) : U.act (pinv s) (U.act s v) = v := by
  obtain ⟨hp, hps, _⟩ := pinv_spec s hs
  rw [act_compose U hp hs, hps, act_id hU hv]

/-- The action maps the vertex list onto itself (membership form). -/
theorem map_act_mem {U : Universe} (hU : U.legal) {s : Perm} (hs : s ∈ perms)
    (v : Vertex) : v ∈ U.vertices.map (U.act s) ↔ v ∈ U.vertices := by
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact act_mem hU hs hw
  · intro h
    obtain ⟨hp, _, hsp⟩ := pinv_spec s hs
    refine List.mem_map.mpr ⟨U.act (pinv s) v, act_mem hU hp h, ?_⟩
    rw [act_compose U hs hp, hsp, act_id hU h]

-- --------------------------------------------- vertex-list and edge basics

theorem vertices_nodup (U : Universe) : U.vertices.Nodup := by
  unfold Universe.vertices
  refine List.Nodup.append ?_ ?_ ?_
  · exact (List.nodup_range).map_on fun x _ y _ h => Vertex.lit.inj h
  · rw [List.nodup_flatMap]
    constructor
    · intro p _
      exact (List.nodup_range).map_on fun x _ y _ h => (Vertex.aux.inj h).2
    · refine List.Pairwise.imp ?_ List.nodup_range
      intro a b hab x hxa hxb
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hxa
      obtain ⟨j', _, heq⟩ := List.mem_map.mp hxb
      exact hab ((Vertex.aux.inj heq).1.symm)
  · intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hy
    obtain ⟨j, _, heq⟩ := List.mem_map.mp hp
    cases heq

theorem unorderedPairs_ne {β : Type} {l : List β} (hnd : l.Nodup) :
    ∀ {x y : β}, (x, y) ∈ unorderedPairs l → x ≠ y := by
  induction l with
  | nil => intro x y h; cases h
  | cons a t ih =>
    intro x y h
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
    unfold unorderedPairs at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨b, hb, heq⟩ := List.mem_map.mp h
      have h1 : a = x := congrArg Prod.fst heq
      have h2 : b = y := congrArg Prod.snd heq
      subst h1; subst h2
      intro hxy
      exact ha (by rw [hxy]; exact hb)
    · exact ih hnd' h

theorem edges_ne {U : Universe} {e : Edge} (he : e ∈ U.edges) : e.1 ≠ e.2 := by
  unfold Universe.edges at he
  obtain ⟨⟨a, b⟩, hab, harm⟩ := List.mem_filterMap.mp he
  have hne : a ≠ b := unorderedPairs_ne (vertices_nodup U) hab
  have he' : e = normEdge (a, b) := by
    revert harm
    split
    · split
      · intro h
        exact (Option.some.inj h).symm
      · intro h
        cases h
    · intro h
      exact (Option.some.inj h).symm
  rw [he']
  unfold normEdge
  dsimp only
  split
  · exact hne
  · exact hne.symm

/-- An invariant edge list is mapped onto itself by every permutation
    (membership form). -/
theorem map_actEdge_mem {U : Universe} (hU : U.legal) {s : Perm}
    (hs : s ∈ perms) {g : List Edge} (hg : ∀ e ∈ g, e ∈ U.edges)
    (hinv : ∀ t ∈ perms, ∀ e ∈ g, U.actEdge t e ∈ g) (e' : Edge) :
    e' ∈ g.map (U.actEdge s) ↔ e' ∈ g := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact hinv s hs e he
  · intro h
    obtain ⟨hp, _, hsp⟩ := pinv_spec s hs
    obtain ⟨h1, h2, hn⟩ := mem_edges (hg e' h)
    refine List.mem_map.mpr ⟨U.actEdge (pinv s) e', hinv (pinv s) hp e' h, ?_⟩
    rw [actEdge_compose hU hs hp h1 h2, hsp, actEdge_id hU h1 h2 hn]

-- --------------------------------------- the edge list is action-closed

/-- The action preserves the vertex kind: auxiliaries stay auxiliaries
    of the same part. -/
theorem act_aux_is_aux (U : Universe) (s : Perm) (p k : Nat) :
    ∃ k', U.act s (Vertex.aux p k) = Vertex.aux p k' := by
  rcases hsz : U.size p with _ | _ | _ | _ | m
  · exact ⟨_, act_aux_reg s k (Or.inl hsz)⟩
  · exact ⟨_, act_aux_one s k hsz⟩
  · exact ⟨_, act_aux_two s k hsz⟩
  · exact ⟨_, act_aux_three s k hsz⟩
  · exact ⟨_, act_aux_reg s k (Or.inr (by omega))⟩

/-- With the literal-literal switch off, no edge joins two literals. -/
theorem lit_pair_not_mem {U : Universe} (hll : U.litLit = false) {e : Edge}
    (he : e ∈ U.edges) {i j : Nat} (h1 : e.1 = Vertex.lit i)
    (h2 : e.2 = Vertex.lit j) : False := by
  unfold Universe.edges at he
  obtain ⟨⟨a, b⟩, _, harm⟩ := List.mem_filterMap.mp he
  cases a with
  | lit ia =>
    cases b with
    | lit ib =>
      rw [hll] at harm
      rw [if_neg Bool.false_ne_true] at harm
      cases harm
    | aux p k =>
      have he' : e = normEdge (Vertex.lit ia, Vertex.aux p k) :=
        (Option.some.inj harm).symm
      rw [he'] at h1 h2
      unfold normEdge at h1 h2
      dsimp only at h1 h2
      by_cases hkey : (Vertex.lit ia).key ≤ (Vertex.aux p k).key
      · rw [if_pos hkey] at h2
        dsimp only at h2
        cases h2
      · rw [if_neg hkey] at h1
        dsimp only at h1
        cases h1
  | aux p k =>
    have he' : e = normEdge (Vertex.aux p k, b) := (Option.some.inj harm).symm
    rw [he'] at h1 h2
    unfold normEdge at h1 h2
    dsimp only at h1 h2
    by_cases hkey : (Vertex.aux p k).key ≤ b.key
    · rw [if_pos hkey] at h1
      dsimp only at h1
      cases h1
    · rw [if_neg hkey] at h2
      dsimp only at h2
      cases h2

theorem mem_unorderedPairs_of {β : Type} {l : List β} {x y : β}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) :
    (x, y) ∈ unorderedPairs l ∨ (y, x) ∈ unorderedPairs l := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hy' : y ∈ t := by
        rcases List.mem_cons.mp hy with rfl | h
        · exact absurd rfl hxy
        · exact h
      left
      unfold unorderedPairs
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨y, hy', rfl⟩))
    · rcases List.mem_cons.mp hy with rfl | hy'
      · right
        unfold unorderedPairs
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x, hx', rfl⟩))
      · rcases ih hx' hy' with h | h
        · left
          unfold unorderedPairs
          exact List.mem_append.mpr (Or.inr h)
        · right
          unfold unorderedPairs
          exact List.mem_append.mpr (Or.inr h)

/-- Completeness of the edge list (litLit off): every normalized pair of
    distinct vertices that is not literal-literal is an edge. -/
theorem mem_edges_of_norm {U : Universe} (hU : U.legal)
    {a b : Vertex} (ha : a ∈ U.vertices) (hb : b ∈ U.vertices) (hab : a ≠ b)
    (hkind : ∀ i j, ¬(a = Vertex.lit i ∧ b = Vertex.lit j)) :
    normEdge (a, b) ∈ U.edges := by
  unfold Universe.edges
  rcases mem_unorderedPairs_of ha hb hab with hp | hp
  · refine List.mem_filterMap.mpr ⟨(a, b), hp, ?_⟩
    cases a with
    | lit ix =>
      cases b with
      | lit iy => exact absurd ⟨rfl, rfl⟩ (hkind ix iy)
      | aux p k => rfl
    | aux p k => rfl
  · refine List.mem_filterMap.mpr ⟨(b, a), hp, ?_⟩
    have hcomm : normEdge (b, a) = normEdge (a, b) := normEdge_comm hU hb ha
    cases b with
    | lit ix =>
      cases a with
      | lit iy => exact absurd ⟨rfl, rfl⟩ (hkind iy ix)
      | aux p k => exact congrArg some hcomm
    | aux p k => exact congrArg some hcomm

/-- The action maps edges to edges (litLit off). -/
theorem actEdge_mem_edges {U : Universe} (hU : U.legal)
    (hll : U.litLit = false) {s : Perm} (hs : s ∈ perms) {e : Edge}
    (he : e ∈ U.edges) : U.actEdge s e ∈ U.edges := by
  obtain ⟨h1, h2, _⟩ := mem_edges he
  show normEdge (U.act s e.1, U.act s e.2) ∈ U.edges
  refine mem_edges_of_norm hU (act_mem hU hs h1) (act_mem hU hs h2)
    (fun h => edges_ne he (act_inj hU hs h1 h2 h)) ?_
  rintro i j ⟨hi, hj⟩
  have hl1 : ∃ i', e.1 = Vertex.lit i' := by
    cases hv : e.1 with
    | lit k => exact ⟨k, rfl⟩
    | aux p k =>
      obtain ⟨k', hk'⟩ := act_aux_is_aux U s p k
      rw [hv, hk'] at hi
      cases hi
  have hl2 : ∃ j', e.2 = Vertex.lit j' := by
    cases hv : e.2 with
    | lit k => exact ⟨k, rfl⟩
    | aux p k =>
      obtain ⟨k', hk'⟩ := act_aux_is_aux U s p k
      rw [hv, hk'] at hj
      cases hj
  obtain ⟨i', hi'⟩ := hl1
  obtain ⟨j', hj'⟩ := hl2
  exact lit_pair_not_mem hll he hi' hj'

theorem edgeOrbit_subset_edges {U : Universe} (hU : U.legal)
    (hll : U.litLit = false) {e : Edge} (he : e ∈ U.edges) :
    ∀ e' ∈ U.edgeOrbit e, e' ∈ U.edges := by
  intro e' he'
  obtain ⟨s, hs, rfl⟩ := mem_edgeOrbit_iff.mp he'
  exact actEdge_mem_edges hU hll hs he

-- ----------------------------------- the orbit generator emits orbits

theorem orbits_go_spec (U : Universe) :
    ∀ (l seen : List Edge), (∀ e ∈ l, e ∈ U.edges) →
      ∀ o ∈ Universe.orbits.go U l seen, ∃ e ∈ U.edges, o = U.edgeOrbit e := by
  intro l
  induction l with
  | nil =>
    intro seen _ o ho
    simp only [Universe.orbits.go] at ho
    cases ho
  | cons e rest ih =>
    intro seen hsub o ho
    simp only [Universe.orbits.go] at ho
    split at ho
    · exact ih seen (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) o ho
    · rcases List.mem_cons.mp ho with rfl | ho'
      · exact ⟨e, hsub e (List.mem_cons_self ..), rfl⟩
      · exact ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) o ho'

/-- Every switch the orbit generator emits is the orbit of an edge. -/
theorem orbits_spec (U : Universe) :
    ∀ o ∈ U.orbits, ∃ e ∈ U.edges, o = U.edgeOrbit e := by
  intro o ho
  exact orbits_go_spec U U.edges [] (fun _ hx => hx) o ho

/-- Every switch of the symmetric walk lives inside the edge list and is
    closed under the action (litLit off). -/
theorem orbit_switch_props {U : Universe} (hU : U.legal)
    (hll : U.litLit = false) {o : List Edge} (ho : o ∈ U.orbits) :
    (∀ e ∈ o, e ∈ U.edges) ∧ ∀ s ∈ perms, ∀ e ∈ o, U.actEdge s e ∈ o := by
  obtain ⟨e₀, he₀, rfl⟩ := orbits_spec U o ho
  refine ⟨edgeOrbit_subset_edges hU hll he₀, ?_⟩
  intro s hs e he
  exact edgeOrbit_closed hU hs (mem_edges he₀).1 (mem_edges he₀).2.1 he

end Atlas
