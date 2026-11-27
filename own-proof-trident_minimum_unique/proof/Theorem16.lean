import proof.Lemma7
import proof.Lemma14
import proof.Lemma15
import proof.TriangleAnalysis
import proof.TridentGadget

/-!
  # Theorem 16 of the paper, by the paper's own proof

  The two results at the end of this file are stated with the definitions of
  `Definition1.lean` only.

  * `trident_is_valid_gadget`: the trident, with its literals and anchors,
    is a valid S3-symmetric clause gadget with six auxiliary vertices.
  * `minimum_unique`: every valid S3-symmetric clause gadget on a finite
    vertex set has at least six auxiliary vertices, added to its six fixed
    vertices (the literals and the anchors), and one with exactly six is
    isomorphic to the trident by an isomorphism that fixes each literal and
    each anchor.

  The proof follows Section IV of the paper and uses no search. Let `G` be a
  valid gadget with the minimum number of auxiliary vertices
  (`minimum_is_trident`); it has at most six, since the trident is valid.

  * Required first layer. A free orbit would use all six auxiliary vertices
    and be the sole auxiliary orbit, which Lemma 15 excludes. By Lemma 11
    some auxiliary vertex has exactly one literal neighbor, and by Lemma 6
    its orbit is then a size-3 orbit with a matched attachment. This orbit
    is isolated by Corollary 12: it is the matched base.
  * Remaining budget. If the other auxiliary vertices do not form a second
    size-3 orbit, they are singletons, possibly with one size-2 orbit.
    Lemma 7 turns the size-2 orbit into two singletons, and Lemma 13
    excludes the family.
  * Equality case. A second size-3 orbit uses all six vertices. Two
    isolated layers are excluded by Lemma 14, and the triangle analysis
    leaves the trident.

  The results are about gadgets on the six fixed vertices of Definition 1
  and count the auxiliary vertices added to them. They are not about
  arbitrary graphs with at most twelve vertices.
-/

namespace Def1

variable {V : Type}

namespace Gadget

variable {g : Gadget V}

/-- With the attachments left by the triangle analysis, the gadget is the
    trident: the indexing of its twelve vertices is a graph isomorphism. -/
theorem TwoLayers.iso_trident (T : g.TwoLayers) (h0 : g.NoLitAnchor) (hPm : T.L.matched)
    (hPc : ¬ T.L.crossed) (hPiso : ¬ T.L.triangle) (hUtri : T.U.triangle)
    (hUlit : ¬ T.U.matched ∧ ¬ T.U.crossed) (hUanch : ∀ t, ¬ T.U.anch t)
    (hw : T.L.wm T.U ∧ ¬ T.L.wc T.U) (hPa : T.L.anch 0 ∧ ¬ T.L.anch 1 ∧ ¬ T.L.anch 2) :
    ∃ e : g.G ≃g trident,
      (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB := by
  have hbij : Function.Bijective T.fr := ⟨T.fr_injective, T.fr_surjective⟩
  have hrel : ∀ a b : TV, T.rel a b ↔ trident.Adj a b := by
    intro a b
    rcases a with i | i | i | _ | _ | _ <;> rcases b with j | j | j | _ | _ | _ <;>
      simp [TwoLayers.rel, trident, SimpleGraph.fromRel_adj, tridentEdge, hPm, hPc, hPiso,
        hUtri, hUlit.1, hUlit.2, hUanch, hw.1, hw.2, hPa.1, hPa.2.1, hPa.2.2]
    -- one case is left: two vertices of the upper triangle
    exact fun h => Or.inl h
  have hsymm : ∀ a, (Equiv.ofBijective T.fr hbij).symm (T.fr a) = a :=
    fun a => (Equiv.ofBijective T.fr hbij).symm_apply_apply a
  refine ⟨⟨(Equiv.ofBijective T.fr hbij).symm, ?_⟩, fun i => hsymm (.x i), hsymm .gT,
    hsymm .gF, hsymm .gB⟩
  intro u v
  obtain ⟨a, rfl⟩ := T.fr_surjective u
  obtain ⟨b, rfl⟩ := T.fr_surjective v
  show trident.Adj ((Equiv.ofBijective T.fr hbij).symm (T.fr a))
    ((Equiv.ofBijective T.fr hbij).symm (T.fr b)) ↔ g.G.Adj (T.fr a) (T.fr b)
  rw [hsymm, hsymm, T.adj_fr h0, hrel]

/-- The matched base with one size-2 orbit `{a, g.ρ τ a}` and singletons.
    A second size-2 orbit would exceed the budget of six auxiliary vertices.
    Lemma 7 turns the size-2 orbit into two singletons, and Lemma 13
    applies. -/
theorem matched_base_pair [Finite V] (g : Gadget V) (hv : g.Valid)
    (hk6 : Nat.card {v // g.IsAux v} ≤ 6) (P : g.Layer) (hPm : P.matched) (hPc : ¬ P.crossed)
    (hPiso : ¬ P.triangle)
    (hW12 : ∀ w, g.IsAux w → (∀ i, w ≠ P.pt i) →
      (∀ σ, g.ρ σ w = w) ∨ (∀ σ, g.ρ σ w = w ↔ Equiv.Perm.sign σ = 1))
    {a : V} (haaux : g.IsAux a) (haP : ∀ i, a ≠ P.pt i)
    (hasign : ∀ σ, g.ρ σ a = a ↔ Equiv.Perm.sign σ = 1) : False := by
  obtain ⟨τ₀, -, hτ₀, -⟩ := exists_swap_fixing 0
  -- the orbit of `a` is `{a, g.ρ τ₀ a}` (Lemma 6)
  obtain ⟨hba, heven, hodd⟩ := g.sign_orbit hasign hτ₀
  have hbaux : g.IsAux (g.ρ τ₀ a) := g.isAux_map τ₀ haaux
  have hbP : ∀ i, g.ρ τ₀ a ≠ P.pt i :=
    fun i h => P.not_mem_map (fun j h' => haP j h'.symm) τ₀ i h.symm
  -- a second size-2 orbit would give seven auxiliary vertices
  have hsing : ∀ w, g.IsAux w → (∀ i, w ≠ P.pt i) → w ≠ a → w ≠ g.ρ τ₀ a →
      ∀ σ, g.ρ σ w = w := by
    intro w hwaux hwP hwa hwb
    rcases hW12 w hwaux hwP with h | h
    · exact h
    · exfalso
      obtain ⟨hw'w, -, -⟩ := g.sign_orbit h hτ₀
      have hw'a : g.ρ τ₀ w ≠ a := by
        intro h1
        have h2 := congrArg (g.ρ τ₀⁻¹) h1
        rw [g.ρ_inv_ρ] at h2
        have h3 := (hodd τ₀⁻¹ (by rw [Equiv.Perm.sign_inv, hτ₀])).1
        exact hwb (h2.trans h3)
      have hw'b : g.ρ τ₀ w ≠ g.ρ τ₀ a := fun h1 => hwa (g.ρ_injective τ₀ h1)
      have hw'P : ∀ i, g.ρ τ₀ w ≠ P.pt i :=
        fun i h1 => P.not_mem_map (fun j h' => hwP j h'.symm) τ₀ i h1.symm
      have hq : Function.Injective
          (fun m : Fin 4 => match m with | 0 => a | 1 => g.ρ τ₀ a | 2 => w | 3 => g.ρ τ₀ w) := by
        intro m n hmn
        fin_cases m <;> fin_cases n <;>
        first
          | rfl
          | exact absurd hmn hba
          | exact absurd hmn.symm hba
          | exact absurd hmn hwa
          | exact absurd hmn.symm hwa
          | exact absurd hmn hwb
          | exact absurd hmn.symm hwb
          | exact absurd hmn hw'a
          | exact absurd hmn.symm hw'a
          | exact absurd hmn hw'b
          | exact absurd hmn.symm hw'b
          | exact absurd hmn hw'w
          | exact absurd hmn.symm hw'w
      have hqP : ∀ (i : Fin 3) (m : Fin 4), P.pt i ≠
          (match m with | 0 => a | 1 => g.ρ τ₀ a | 2 => w | 3 => g.ρ τ₀ w) := by
        intro i m
        fin_cases m
        · exact fun h1 => haP i h1.symm
        · exact fun h1 => hbP i h1.symm
        · exact fun h1 => hwP i h1.symm
        · exact fun h1 => hw'P i h1.symm
      have hqaux : ∀ m : Fin 4, g.IsAux
          (match m with | 0 => a | 1 => g.ρ τ₀ a | 2 => w | 3 => g.ρ τ₀ w) := by
        intro m
        fin_cases m
        · exact haaux
        · exact hbaux
        · exact hwaux
        · exact g.isAux_map τ₀ hwaux
      have hinj : Function.Injective (Sum.elim P.pt
          (fun m : Fin 4 => match m with | 0 => a | 1 => g.ρ τ₀ a | 2 => w | 3 => g.ρ τ₀ w)) := by
        intro x y hxy
        rcases x with i | m <;> rcases y with j | n
        · exact congrArg Sum.inl (P.inj hxy)
        · exact absurd hxy (hqP i n)
        · exact absurd hxy.symm (hqP j m)
        · exact congrArg Sum.inr (hq hxy)
      have hge := g.card_aux_ge _ hinj (by
        rintro (i | m)
        · exact P.aux i
        · exact hqaux m)
      have hc : Fintype.card (Fin 3 ⊕ Fin 4) = 7 := by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      omega
  -- Lemma 7: an action that fixes a and its partner
  obtain ⟨-, g', hadj, hlit, hT, hF, hB, hab, hrest⟩ :=
    g.lemma7 haaux hbaux heven hodd (by
      intro w hwaux hwa hwb
      by_cases hwP : ∃ i, w = P.pt i
      · obtain ⟨i, rfl⟩ := hwP
        exact Or.inr ⟨i, fun σ => by rw [P.map]; exact P.inj.eq_iff⟩
      · exact Or.inl (hsing w hwaux (fun i hi => hwP ⟨i, hi⟩) hwa hwb))
  have hvalid' : g'.Valid := by
    intro α
    rw [← hv α]
    simp only [Gadget.Extends, hadj, hlit, hT, hF, hB]
  have haux' : ∀ w, g'.IsAux w ↔ g.IsAux w := by
    intro w
    simp only [Gadget.IsAux, hlit, hT, hF, hB]
  -- Lemma 13 for the new action: the matched base with singletons
  refine g'.lemma13
    { pt := P.pt
      map := fun σ i => (hrest σ (P.pt i) (fun h => haP i h.symm) (fun h => hbP i h.symm)).trans
        (P.map σ i)
      inj := P.inj
      aux := fun i => (haux' _).mpr (P.aux i) } ?_ ?_ ?_ ?_ hvalid'
  · show g'.G.Adj (P.pt 0) (g'.lit 0)
    rw [hadj, hlit]
    exact hPm
  · intro h
    have h1 : g'.G.Adj (P.pt 0) (g'.lit 1) := h
    rw [hadj, hlit] at h1
    exact hPc h1
  · intro h
    have h1 : g'.G.Adj (P.pt 0) (P.pt 1) := h
    rw [hadj] at h1
    exact hPiso h1
  · intro w hw' hwP σ
    by_cases hwa : w = a
    · rw [hwa]
      exact (hab σ).1
    · by_cases hwb : w = g.ρ τ₀ a
      · rw [hwb]
        exact (hab σ).2
      · rw [hrest σ w hwa hwb]
        exact hsing w ((haux' w).mp hw') hwP hwa hwb σ

/-- The proof of Theorem 16 for a minimum valid gadget: it has six auxiliary
    vertices and it is the trident. -/
theorem minimum_is_trident [Finite V] (g : Gadget V) (hv : g.Valid) (hmin : g.IsMinimum) :
    Nat.card {v // g.IsAux v} = 6 ∧ ∃ e : g.G ≃g trident,
      (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB := by
  have h0 := hv.noLitAnchor
  -- the trident is valid with six auxiliary vertices, so g has at most six
  have hk6 : Nat.card {v // g.IsAux v} ≤ 6 := hmin.card_le_six
  -- Required first layer. A free orbit would use all six auxiliary vertices
  -- and be the sole auxiliary orbit, which Lemma 15 excludes.
  have hnofree : ∀ w, g.IsAux w → ¬ ∀ σ, g.ρ σ w = w ↔ σ = 1 := by
    intro w hwaux hfree
    have hinj : Function.Injective fun σ : Equiv.Perm (Fin 3) => g.ρ σ w := by
      intro σ τ h
      have h1 := (g.ρ_eq_ρ_iff σ τ w).mp h
      rw [hfree] at h1
      exact (inv_mul_eq_one.mp h1).symm
    have hc : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      rfl
    have hsole := g.aux_surj _ hinj (fun σ => g.isAux_map σ hwaux) (by rw [hc]; exact hk6)
    exact g.lemma15 hv hmin hwaux hsole hfree
  -- Lemmas 6 and 11 therefore require a size-3 orbit with a matched literal
  -- attachment: take an auxiliary vertex with exactly one literal neighbor
  obtain ⟨v, hvaux, k, hk⟩ := g.lemma11 hv
  have hnotfix : ¬ ∀ σ, Equiv.Perm.sign σ = 1 → g.ρ σ v = v := by
    intro hfix
    obtain ⟨j, hjk, -⟩ := exists_third k k
    exact hjk ((hk j).mp ((g.adj_lit_of_even_fixed hfix k j).mp ((hk k).mpr rfl)))
  rcases g.stab_cases v with hall | hsign | ⟨k', hnat⟩ | hfree
  · exact absurd (fun σ _ => hall σ) hnotfix
  · exact absurd (fun σ hσ => (hsign σ).mpr hσ) hnotfix
  · -- its orbit is a size-3 orbit, and the attachment is matched
    have hkk : k' = k := by
      by_contra hne
      obtain ⟨τ, hτ, -, hmove⟩ := exists_swap_fixing k'
      have h1 := (g.adj_ρ τ).mpr ((hk k).mpr rfl)
      rw [(hnat τ).mpr hτ, g.ρ_lit] at h1
      exact hmove k (fun h => hne h.symm) ((hk (τ k)).mp h1)
    rw [hkk] at hnat
    obtain ⟨P, hPv⟩ : ∃ P : g.Layer, P.pt k = v := ⟨_, Layer.ofNatural_pt g hvaux hnat⟩
    have hPadj : ∀ j, g.G.Adj (P.pt k) (g.lit j) ↔ j = k := by
      rw [hPv]
      exact hk
    have hPm : P.matched := by
      have h1 := (P.adj_lit k k).mp ((hPadj k).mpr rfl)
      rwa [if_pos rfl] at h1
    have hPc : ¬ P.crossed := by
      intro hc'
      obtain ⟨j, hjk, -⟩ := exists_third k k
      exact hjk ((hPadj j).mp ((P.adj_lit k j).mpr (by rwa [if_neg (Ne.symm hjk)])))
    -- it is an isolated layer by Corollary 12: the matched base
    have hPiso : ¬ P.triangle := fun htri => cor12 P htri (Or.inl hPm) hv.allTrue
    by_cases hW3 : ∃ w, g.IsAux w ∧ (∀ i, w ≠ P.pt i) ∧
        ∃ kw : Fin 3, ∀ σ, g.ρ σ w = w ↔ σ kw = kw
    · -- Equality case. A second size-3 orbit exhausts the six-vertex budget.
      obtain ⟨w, hwaux, hwP, kw, hnatw⟩ := hW3
      obtain ⟨U, hUw⟩ : ∃ U : g.Layer, U.pt kw = w := ⟨_, Layer.ofNatural_pt g hwaux hnatw⟩
      have hdisj : ∀ i j, P.pt i ≠ U.pt j :=
        P.disjoint_of_not_mem U (j0 := kw) (by
          rw [hUw]
          exact fun i h => hwP i h.symm)
      obtain ⟨hcard, hallT⟩ := two_layers_exhaust_budget hmin P U hdisj
      refine ⟨hcard, ?_⟩
      by_cases hUtri : U.triangle
      · -- the second layer is a triangle: the triangle analysis leaves the trident
        obtain ⟨hUlit, hUanch, hw, hPa⟩ :=
          triangle_analysis ⟨P, U, hdisj, hallT⟩ hv hmin hPm hPc hPiso hUtri
        exact TwoLayers.iso_trident ⟨P, U, hdisj, hallT⟩ h0 hPm hPc hPiso hUtri hUlit hUanch
          hw hPa
      · -- two isolated layers are excluded by Lemma 14
        exact (lemma14 hv hmin P U hdisj hPiso hUtri).elim
    · -- Remaining budget. The other auxiliary vertices do not form a second
      -- size-3 orbit: they are singletons, possibly with one size-2 orbit.
      exfalso
      have hW12 : ∀ w, g.IsAux w → (∀ i, w ≠ P.pt i) →
          (∀ σ, g.ρ σ w = w) ∨ (∀ σ, g.ρ σ w = w ↔ Equiv.Perm.sign σ = 1) := by
        intro w hwaux hwP
        rcases g.stab_cases w with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd ⟨w, hwaux, hwP, h⟩ hW3
        · exact absurd h (hnofree w hwaux)
      by_cases hW2 : ∃ a, g.IsAux a ∧ (∀ i, a ≠ P.pt i) ∧
          ∀ σ, g.ρ σ a = a ↔ Equiv.Perm.sign σ = 1
      · -- Lemma 7 includes the size-2 orbit in the singleton family
        obtain ⟨a, haaux, haP, hasign⟩ := hW2
        exact matched_base_pair g hv hk6 P hPm hPc hPiso hW12 haaux haP hasign
      · -- Lemma 13 excludes the singleton family
        refine g.lemma13 P hPm hPc hPiso (fun w hwaux hwP => ?_) hv
        rcases hW12 w hwaux hwP with h | h
        · exact h
        · exact absurd ⟨w, hwaux, hwP, h⟩ hW2
  · exact absurd hfree (hnofree v hvaux)

end Gadget

-- ------------------------------------------------------------- the theorem

/-- Theorem 16 of the paper (minimum size and uniqueness), for Definition 1.
    Let `g` be a valid S3-symmetric clause gadget on a finite vertex set:
    its six fixed vertices are the three literals and the three anchors, and
    its other vertices are auxiliary. Then `g` has at least six auxiliary
    vertices, and so at least twelve vertices in total. If it has exactly
    six auxiliary vertices, it is the trident: there is a graph isomorphism
    onto the trident that sends each literal to the corresponding literal
    and each anchor to the corresponding anchor. -/
theorem minimum_unique [Fintype V] (g : Gadget V) (hv : g.Valid) :
    6 ≤ Nat.card {v // g.IsAux v} ∧ 12 ≤ Fintype.card V ∧
    (Nat.card {v // g.IsAux v} = 6 → ∃ e : g.G ≃g trident,
      (∀ i, e (g.lit i) = TV.x i) ∧ e g.gT = TV.gT ∧ e g.gF = TV.gF ∧ e g.gB = TV.gB) := by
  classical
  -- a valid gadget with the minimum number of auxiliary vertices
  have hex : ∃ n, ∃ (V' : Type) (_ : Finite V') (g' : Gadget V'),
      g'.Valid ∧ Nat.card {v // g'.IsAux v} = n := ⟨_, V, inferInstance, g, hv, rfl⟩
  obtain ⟨V₀, hfin, g₀, hv₀, hn₀⟩ := Nat.find_spec hex
  have hmin₀ : g₀.IsMinimum := by
    intro V' _ g' hv'
    rw [hn₀]
    exact Nat.find_min' hex ⟨V', inferInstance, g', hv', rfl⟩
  -- it has six auxiliary vertices
  have h6 : Nat.find hex = 6 := by
    rw [← hn₀]
    exact (Gadget.minimum_is_trident g₀ hv₀ hmin₀).1
  have hsix : 6 ≤ Nat.card {v // g.IsAux v} := by
    rw [← h6]
    exact Nat.find_min' hex ⟨V, inferInstance, g, hv, rfl⟩
  have hcard : Fintype.card V = Nat.card {v // g.IsAux v} + 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact g.card_eq
  refine ⟨hsix, by omega, fun h => ?_⟩
  -- a valid gadget with six auxiliary vertices is minimum
  have hmin : g.IsMinimum := by
    intro V' _ g' hv'
    rw [h, ← h6]
    exact Nat.find_min' hex ⟨V', inferInstance, g', hv', rfl⟩
  exact (Gadget.minimum_is_trident g hv hmin).2

/-- The trident attains the minimum: the trident graph, with the literals
    `TV.x i` and the anchors `TV.gT`, `TV.gF`, `TV.gB`, carries an
    S3-symmetric clause gadget in the sense of Definition 1, this gadget is
    valid, and it has six auxiliary vertices (the `TV.p i` and the
    `TV.u i`), twelve vertices in total. -/
theorem trident_is_valid_gadget :
    (∃ g : Gadget TV, g.G = trident ∧ g.lit = TV.x ∧ g.gT = TV.gT ∧ g.gF = TV.gF ∧
      g.gB = TV.gB ∧ g.Valid ∧ Nat.card {v // g.IsAux v} = 6) ∧ Fintype.card TV = 12 :=
  ⟨⟨tridentGadget, rfl, rfl, rfl, rfl, rfl, tridentGadget_valid, tridentGadget_card_aux⟩,
    card_TV⟩

end Def1

-- The build prints the axioms of the two theorems,
#print axioms Def1.trident_is_valid_gadget
#print axioms Def1.minimum_unique

-- and it fails if they are not exactly the three standard axioms.
/--
info: 'Def1.trident_is_valid_gadget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.trident_is_valid_gadget

/--
info: 'Def1.minimum_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Def1.minimum_unique
