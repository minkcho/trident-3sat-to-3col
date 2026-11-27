import proof.Lemma6

/-!
  Gadgets whose auxiliary vertices are two size-3 orbits.

  `TwoLayers` holds two disjoint layers `L` and `U` that contain all the
  auxiliary vertices. The twelve vertices are then indexed by the vertex
  type `TV` of the trident (`fr`): `x i` is literal `i`, `p i` and `u i` are
  the vertices of `L` and `U`, and the three anchors. By Lemma 6 the edges
  are described by the attachment flags of the two layers (`rel`,
  `adj_fr`). `coloring_of` builds a coloring from its values on the twelve
  indices.
-/

namespace Def1

variable {V : Type}

namespace Gadget

/-- Two disjoint size-3 orbits that contain all auxiliary vertices. -/
structure TwoLayers (g : Gadget V) where
  L : g.Layer
  U : g.Layer
  disj : ∀ i j, L.pt i ≠ U.pt j
  all : ∀ w, g.IsAux w → (∃ i, w = L.pt i) ∨ ∃ i, w = U.pt i

variable {g : Gadget V}

namespace TwoLayers

variable (T : g.TwoLayers)

/-- The twelve vertices, indexed by the vertices of the trident. -/
def fr : TV → V
  | .x i => g.lit i
  | .p i => T.L.pt i
  | .u i => T.U.pt i
  | .gT => g.anchor 0
  | .gF => g.anchor 1
  | .gB => g.anchor 2

theorem fr_injective : Function.Injective T.fr := by
  intro a b h
  rcases a with i | i | i | _ | _ | _ <;> rcases b with j | j | j | _ | _ | _ <;>
  dsimp only [fr] at h <;>
  first
    | rfl
    | exact congrArg TV.x (g.lit_inj h)
    | exact congrArg TV.p (T.L.inj h)
    | exact congrArg TV.u (T.U.inj h)
    | exact absurd h (T.L.pt_ne_lit _ _)
    | exact absurd h.symm (T.L.pt_ne_lit _ _)
    | exact absurd h (T.U.pt_ne_lit _ _)
    | exact absurd h.symm (T.U.pt_ne_lit _ _)
    | exact absurd h (g.lit_ne_anchor' _ _)
    | exact absurd h.symm (g.lit_ne_anchor' _ _)
    | exact absurd h (T.disj _ _)
    | exact absurd h.symm (T.disj _ _)
    | exact absurd h (T.L.pt_ne_anchor _ _)
    | exact absurd h.symm (T.L.pt_ne_anchor _ _)
    | exact absurd h (T.U.pt_ne_anchor _ _)
    | exact absurd h.symm (T.U.pt_ne_anchor _ _)
    | exact absurd (g.anchor_injective h) (by decide)

theorem fr_surjective : Function.Surjective T.fr := by
  intro v
  rcases g.vertex_cases v with ⟨i, rfl⟩ | ⟨t, rfl⟩ | hv
  · exact ⟨.x i, rfl⟩
  · fin_cases t
    · exact ⟨.gT, rfl⟩
    · exact ⟨.gF, rfl⟩
    · exact ⟨.gB, rfl⟩
  · rcases T.all v hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨.p i, rfl⟩
    · exact ⟨.u i, rfl⟩

/-- The edges in terms of the attachment flags of the two layers, under the
    standing assumption. -/
def rel : TV → TV → Prop
  | .x _, .x _ => False
  | .x i, .p j => if i = j then T.L.matched else T.L.crossed
  | .x i, .u j => if i = j then T.U.matched else T.U.crossed
  | .x _, .gT => False
  | .x _, .gF => False
  | .x _, .gB => True
  | .p i, .x j => if j = i then T.L.matched else T.L.crossed
  | .p i, .p j => i ≠ j ∧ T.L.triangle
  | .p i, .u j => if i = j then T.L.wm T.U else T.L.wc T.U
  | .p _, .gT => T.L.anch 0
  | .p _, .gF => T.L.anch 1
  | .p _, .gB => T.L.anch 2
  | .u i, .x j => if j = i then T.U.matched else T.U.crossed
  | .u i, .p j => if j = i then T.L.wm T.U else T.L.wc T.U
  | .u i, .u j => i ≠ j ∧ T.U.triangle
  | .u _, .gT => T.U.anch 0
  | .u _, .gF => T.U.anch 1
  | .u _, .gB => T.U.anch 2
  | .gT, .x _ => False
  | .gT, .p _ => T.L.anch 0
  | .gT, .u _ => T.U.anch 0
  | .gT, .gT => False
  | .gT, .gF => True
  | .gT, .gB => True
  | .gF, .x _ => False
  | .gF, .p _ => T.L.anch 1
  | .gF, .u _ => T.U.anch 1
  | .gF, .gT => True
  | .gF, .gF => False
  | .gF, .gB => True
  | .gB, .x _ => True
  | .gB, .p _ => T.L.anch 2
  | .gB, .u _ => T.U.anch 2
  | .gB, .gT => True
  | .gB, .gF => True
  | .gB, .gB => False

/-- Lemma 6 for two layers: adjacency is given by the flags. -/
theorem adj_fr (h0 : g.NoLitAnchor) (a b : TV) : g.G.Adj (T.fr a) (T.fr b) ↔ T.rel a b := by
  have hirr : ∀ x : V, ¬ g.G.Adj x x := fun x => g.G.irrefl
  have hsw : ∀ (M : g.Layer) (i j : Fin 3), g.G.Adj (M.pt i) (g.lit j) ↔
      if j = i then M.matched else M.crossed := by
    intro M i j
    rw [M.adj_lit i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (fun h => hij h.symm)]
  rcases a with i | i | i | _ | _ | _ <;> rcases b with j | j | j | _ | _ | _
  -- a = x i
  · exact ⟨fun h => absurd h (g.lit_nonadj i j), False.elim⟩
  · exact (g.G.adj_comm _ _).trans (hsw T.L j i)
  · exact (g.G.adj_comm _ _).trans (hsw T.U j i)
  · exact ⟨fun h => (h0 i).1 h, False.elim⟩
  · exact ⟨fun h => (h0 i).2 h, False.elim⟩
  · exact ⟨fun _ => trivial, fun _ => (g.fan i).symm⟩
  -- a = p i
  · exact hsw T.L i j
  · exact T.L.adj_self i j
  · exact T.L.adj_layer T.U i j
  · exact T.L.adj_anchor i 0
  · exact T.L.adj_anchor i 1
  · exact T.L.adj_anchor i 2
  -- a = u i
  · exact hsw T.U i j
  · exact (g.G.adj_comm _ _).trans (T.L.adj_layer T.U j i)
  · exact T.U.adj_self i j
  · exact T.U.adj_anchor i 0
  · exact T.U.adj_anchor i 1
  · exact T.U.adj_anchor i 2
  -- a = gT
  · exact ⟨fun h => (h0 j).1 h.symm, False.elim⟩
  · exact (g.G.adj_comm _ _).trans (T.L.adj_anchor j 0)
  · exact (g.G.adj_comm _ _).trans (T.U.adj_anchor j 0)
  · exact ⟨fun h => hirr _ h, False.elim⟩
  · exact ⟨fun _ => trivial, fun _ => g.palette.1⟩
  · exact ⟨fun _ => trivial, fun _ => g.palette.2.2.symm⟩
  -- a = gF
  · exact ⟨fun h => (h0 j).2 h.symm, False.elim⟩
  · exact (g.G.adj_comm _ _).trans (T.L.adj_anchor j 1)
  · exact (g.G.adj_comm _ _).trans (T.U.adj_anchor j 1)
  · exact ⟨fun _ => trivial, fun _ => g.palette.1.symm⟩
  · exact ⟨fun h => hirr _ h, False.elim⟩
  · exact ⟨fun _ => trivial, fun _ => g.palette.2.1⟩
  -- a = gB
  · exact ⟨fun _ => trivial, fun _ => g.fan j⟩
  · exact (g.G.adj_comm _ _).trans (T.L.adj_anchor j 2)
  · exact (g.G.adj_comm _ _).trans (T.U.adj_anchor j 2)
  · exact ⟨fun _ => trivial, fun _ => g.palette.2.2⟩
  · exact ⟨fun _ => trivial, fun _ => g.palette.2.1.symm⟩
  · exact ⟨fun h => hirr _ h, False.elim⟩

/-- A coloring given by its values on the twelve indices. -/
theorem coloring_of {α : Fin 3 → Bool} (col : TV → Fin 3) (hT : col .gT = 0)
    (hF : col .gF = 1) (hB : col .gB = 2) (hx : ∀ i, col (.x i) = if α i then 0 else 1)
    (hp : ∀ a b, g.G.Adj (T.fr a) (T.fr b) → col a ≠ col b) : ∃ c, g.IsColoring α c := by
  have hbij : Function.Bijective T.fr := ⟨T.fr_injective, T.fr_surjective⟩
  have key : ∀ a, col ((Equiv.ofBijective T.fr hbij).symm (T.fr a)) = col a := by
    intro a
    have h1 : (Equiv.ofBijective T.fr hbij).symm (T.fr a) = a :=
      (Equiv.ofBijective T.fr hbij).symm_apply_apply a
    rw [h1]
  refine ⟨fun v => col ((Equiv.ofBijective T.fr hbij).symm v), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    obtain ⟨a, rfl⟩ := T.fr_surjective u
    obtain ⟨b, rfl⟩ := T.fr_surjective v
    show col ((Equiv.ofBijective T.fr hbij).symm (T.fr a)) ≠
      col ((Equiv.ofBijective T.fr hbij).symm (T.fr b))
    rw [key, key]
    exact hp a b huv
  · exact (key .gT).trans hT
  · exact (key .gF).trans hF
  · exact (key .gB).trans hB
  · intro i
    exact (key (.x i)).trans (hx i)

/-- Under (F, F, F): a coloring with one color `a` on `L` and one color `b`
    on `U`, for two isolated layers. The color F is allowed only on a layer
    without literal neighbors, a layer avoids the color of its anchor, and
    equal colors need an empty wiring. -/
theorem uniform_allFalse (h0 : g.NoLitAnchor) (hL : ¬ T.L.triangle) (hU : ¬ T.U.triangle)
    (a b : Fin 3) (haL : a = 1 → ¬ T.L.matched ∧ ¬ T.L.crossed)
    (hbU : b = 1 → ¬ T.U.matched ∧ ¬ T.U.crossed) (haA : ¬ T.L.anch a) (hbA : ¬ T.U.anch b)
    (hab : a = b → ¬ T.L.wm T.U ∧ ¬ T.L.wc T.U) : ∃ c, g.IsColoring allFalse c := by
  have h1a : ∀ {q : Prop} [Decidable q], (if q then T.L.matched else T.L.crossed) →
      (1 : Fin 3) ≠ a := by
    intro q _ h ha
    have h2 := haL ha.symm
    split at h
    · exact h2.1 h
    · exact h2.2 h
  have h1b : ∀ {q : Prop} [Decidable q], (if q then T.U.matched else T.U.crossed) →
      (1 : Fin 3) ≠ b := by
    intro q _ h hb
    have h2 := hbU hb.symm
    split at h
    · exact h2.1 h
    · exact h2.2 h
  have hw : ∀ {q : Prop} [Decidable q], (if q then T.L.wm T.U else T.L.wc T.U) → a ≠ b := by
    intro q _ h hab'
    have h2 := hab hab'
    split at h
    · exact h2.1 h
    · exact h2.2 h
  have hLa : ∀ t, T.L.anch t → a ≠ t := fun t ht h => haA (h ▸ ht)
  have hUb : ∀ t, T.U.anch t → b ≠ t := fun t ht h => hbA (h ▸ ht)
  refine T.coloring_of (α := allFalse)
    (fun v => match v with
      | .x _ => 1 | .p _ => a | .u _ => b | .gT => 0 | .gF => 1 | .gB => 2)
    rfl rfl rfl (fun _ => rfl) ?_
  intro x y hxy
  rw [T.adj_fr h0] at hxy
  rcases x with i | i | i | _ | _ | _ <;> rcases y with j | j | j | _ | _ | _ <;>
  dsimp only <;>
  first
    | exact False.elim hxy
    | exact absurd hxy.2 hL
    | exact absurd hxy.2 hU
    | exact h1a hxy
    | exact (h1a hxy).symm
    | exact h1b hxy
    | exact (h1b hxy).symm
    | exact hw hxy
    | exact (hw hxy).symm
    | exact hLa _ hxy
    | exact (hLa _ hxy).symm
    | exact hUb _ hxy
    | exact (hUb _ hxy).symm
    | decide

end TwoLayers

end Gadget

end Def1
