import atlas.ProofsWalkBridge
import atlas.ProofsSym
/-!
  P3-3: exhaustiveness of a SHARDED sweep.

  `searchSlice P parts symmetry shards shard` pre-decides the first
  log2(shards) free switches by the bits of `shard` (`shardSplit`); a
  shard index beyond the slice's own switch count names an empty part.
  This file proves that the shards cover the candidate space: every
  enumerated graph of the slice is, up to permutation of its edge list, a
  leaf of the shard named by its low bits (`graphAt_shard_perm`;
  [opus5.5 review] was "partition"/"exactly": disjointness holds by
  construction but is not proved, and the exhaustiveness lift needs only coverage),
  and lifts the P3 exhaustiveness theorem accordingly -- if every shard of
  a 2^b-way split reports nothing, `gadgetK` rejects every graph of the
  slice (`searchSlice_sharded_exhaustive_threeColoring_graphs`), for
  every slice, every b ≥ 1 and every parts, and its raw-table lift through the
  P4 symmetry reduction (`searchSlice_sharded_symmetric_covers_raw`). The
  runtime test `testShards` checked this at two slices.
-/

namespace Atlas

open List

-- ------------------------------------------------- bitSubset by index

/-- `bitSubset` over an append reads the mask on the first list and the
    shifted mask on the second. -/
theorem bitSubset_append {α : Type} (l₁ l₂ : List α) :
    ∀ m, bitSubset m (l₁ ++ l₂) = bitSubset m l₁ ++ bitSubset (m >>> l₁.length) l₂ := by
  induction l₁ with
  | nil => intro m; simp [bitSubset]
  | cons x l ih =>
    intro m
    show (if m &&& 1 == 1 then [x] else []) ++ bitSubset (m >>> 1) (l ++ l₂)
      = ((if m &&& 1 == 1 then [x] else []) ++ bitSubset (m >>> 1) l)
        ++ bitSubset (m >>> (l.length + 1)) l₂
    rw [ih (m >>> 1), List.append_assoc, Nat.add_comm l.length 1, Nat.shiftRight_add]

/-- `bitSubset` reads only the bits below the list's length. -/
theorem bitSubset_congr {α : Type} (l : List α) :
    ∀ m m', (∀ i, i < l.length → (m >>> i &&& 1 == 1) = (m' >>> i &&& 1 == 1)) →
      bitSubset m l = bitSubset m' l := by
  induction l with
  | nil => intros; rfl
  | cons x l ih =>
    intro m m' h
    show (if m &&& 1 == 1 then [x] else []) ++ bitSubset (m >>> 1) l
      = (if m' &&& 1 == 1 then [x] else []) ++ bitSubset (m' >>> 1) l
    have h0 := h 0 (Nat.succ_pos _)
    simp only [Nat.shiftRight_zero] at h0
    rw [h0, ih (m >>> 1) (m' >>> 1)]
    intro i hi
    have := h (i + 1) (Nat.succ_lt_succ hi)
    rw [Nat.add_comm i 1, Nat.shiftRight_add, Nat.shiftRight_add] at this
    exact this

/-- The shard fold: pre-deciding the switches of a list by a mask stacks
    the selected switches (reversed) in front of the base. -/
theorem shardFold_eq (m : Nat) (f : List Edge → Nat × List Edge → List Edge)
    (hf : ∀ b j g, f b (j, g) = if m >>> j &&& 1 == 1 then g ++ b else b) :
    ∀ (l : List (List Edge)) (k : Nat) (init : List Edge),
      ((List.range' k l.length).zip l).foldl f init
        = (bitSubset (m >>> k) l).reverse.flatten ++ init := by
  intro l
  induction l with
  | nil => intro k init; simp [bitSubset]
  | cons x l ih =>
    intro k init
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons, hf, ih (k + 1)]
    show (bitSubset (m >>> (k + 1)) l).reverse.flatten
        ++ (if m >>> k &&& 1 == 1 then x ++ init else init)
      = ((if (m >>> k) &&& 1 == 1 then [x] else [])
          ++ bitSubset ((m >>> k) >>> 1) l).reverse.flatten ++ init
    rw [← Nat.shiftRight_add, List.reverse_append, List.flatten_append, List.append_assoc]
    congr 1
    split <;> simp

/-- `shardSplit`, characterized: the base gains the selected low switches,
    the free list loses them. -/
theorem shardSplit_eq (base : List Edge) (free : List (List Edge))
    (shards shard : Nat) :
    shardSplit base free shards shard
      = ((bitSubset shard (free.take (Nat.min (Nat.log2 shards) free.length))).reverse.flatten
          ++ base,
         free.drop (Nat.min (Nat.log2 shards) free.length)) := by
  unfold shardSplit
  dsimp only
  set bits := Nat.min (Nat.log2 shards) free.length with hb
  have hlen : (free.take bits).length = bits := by
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.min_le_right _ _)
  refine Prod.ext ?_ rfl
  rw [List.range_eq_range', show List.range' 0 bits = List.range' 0 (free.take bits).length by
    rw [hlen]]
  refine (shardFold_eq shard _ (fun _ _ _ => rfl) (free.take bits) 0 base).trans ?_
  rw [Nat.shiftRight_zero]

-- ------------------------------------ the shards cover the slice
-- [opus5.5 review] header was "partition"

/-- Every enumerated graph of the slice is, up to permutation, a leaf of
    the shard named by its low bits: shard `mask % 2^bits` at the mask
    `mask >>> bits`. -/
theorem graphAt_shard_perm (base : List Edge) (free : List (List Edge))
    (b mask : Nat) :
    (graphAt (shardSplit base free (2 ^ b) (mask % 2 ^ Nat.min b free.length)).1
        (shardSplit base free (2 ^ b) (mask % 2 ^ Nat.min b free.length)).2
        (mask >>> Nat.min b free.length)).Perm (graphAt base free mask) := by
  rw [shardSplit_eq, Nat.log2_two_pow]
  set bits := Nat.min b free.length with hbits
  have hle : bits ≤ free.length := Nat.min_le_right _ _
  have hlen : (free.take bits).length = bits := by rw [List.length_take]; omega
  have hsplit : bitSubset mask free
      = bitSubset (mask % 2 ^ bits) (free.take bits)
        ++ bitSubset (mask >>> bits) (free.drop bits) := by
    conv_lhs => rw [← List.take_append_drop bits free]
    rw [bitSubset_append, hlen]
    congr 1
    apply bitSubset_congr
    intro i hi
    rw [hlen] at hi
    rw [bit_eq_testBit, bit_eq_testBit, Nat.testBit_mod_two_pow, decide_eq_true hi,
      Bool.true_and]
  unfold graphAt
  rw [graphAt_selector, graphAt_selector, hsplit, List.flatten_append]
  calc ((bitSubset (mask % 2 ^ bits) (free.take bits)).reverse.flatten ++ base)
        ++ (bitSubset (mask >>> bits) (free.drop bits)).flatten
      ~ (base ++ (bitSubset (mask % 2 ^ bits) (free.take bits)).reverse.flatten)
        ++ (bitSubset (mask >>> bits) (free.drop bits)).flatten :=
        List.perm_append_comm.append_right _
    _ ~ (base ++ (bitSubset (mask % 2 ^ bits) (free.take bits)).flatten)
        ++ (bitSubset (mask >>> bits) (free.drop bits)).flatten :=
        ((List.reverse_perm _).flatten.append_left base).append_right _
    _ = base ++ ((bitSubset (mask % 2 ^ bits) (free.take bits)).flatten
        ++ (bitSubset (mask >>> bits) (free.drop bits)).flatten) := by
        rw [List.append_assoc]

-- ------------------------------------------- the sharded walk, unfolded

/-- A live shard of a 2^b-way split runs the walk on its split. -/
theorem searchSlice_found_shard (P : Problem) (parts : List Nat) (symmetry : Bool)
    (b shard : Nat) (hb : 0 < b)
    (hneg : negLayerOk P (P.attach parts).1 = true)
    (hlive : shard >>> Nat.min b
      ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).2.length = 0) :
    (searchSlice P parts symmetry (2 ^ b) shard).2.found
      = ((searchAux P (P.attach parts).1 (anchorsOf parts.length (P.attach parts).1)
          (gadgetRows P symmetry)
          (shardSplit ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).1
            ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).2 (2 ^ b) shard).2
          (shardSplit ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).1
            ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).2 (2 ^ b) shard).1
          { total := 2 ^ (shardSplit
              ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).1
              ((P.attach parts).1.splitForced (P.attach parts).2 symmetry).2
              (2 ^ b) shard).2.length }).found).reverse := by
  have h1 : (1 < 2 ^ b) = True := eq_true (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hb))
  have h2 : (2 ^ b ≤ 1) = False := eq_false (Nat.not_le.mpr
    (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hb)))
  unfold searchSlice
  rcases hUf : P.attach parts with ⟨U, forced⟩
  rw [hUf] at hneg hlive
  simp only [hneg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.log2_two_pow, hlive,
    bne_self_eq_false, Bool.and_false, h2, h1, decide_true]

-- --------------------------------------- the sharded exhaustiveness

/-- P3 for a sharded sweep: if every shard of a 2^b-way split of the
    3-coloring slice reports nothing, `gadgetK` rejects every graph of the
    slice -- the shards cover the candidate space ([opus5.5 review] was
    "partition"). -/
theorem searchSlice_sharded_exhaustive_threeColoring_graphs (parts : List Nat)
    (symmetry : Bool) (b : Nat) (hb : 0 < b)
    (h : ∀ i, i < 2 ^ b →
      (searchSlice threeColoring parts symmetry (2 ^ b) i).2.found = []) :
    ∀ g ∈ (threeColoring.attach parts).1.graphs (symmetry := symmetry)
        (forced := (threeColoring.attach parts).2),
      gadgetK threeColoring parts g symmetry = none := by
  intro g hg
  unfold Universe.graphs at hg
  obtain ⟨mask, _, rfl⟩ := List.mem_map.mp hg
  have hi : mask % 2 ^ Nat.min b
      ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 symmetry).2.length
      < 2 ^ b :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
  have hlive : (mask % 2 ^ Nat.min b
      ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 symmetry).2.length)
      >>> Nat.min b
      ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 symmetry).2.length
      = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
  have hfound := h _ hi
  rw [searchSlice_found_shard threeColoring parts symmetry b _ hb rfl hlive,
    List.reverse_eq_nil_iff] at hfound
  rw [gadgetK_3col_eq]
  cases hchk : checkGadget threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry)
      (graphAt ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 mask) with
  | none => exact hchk
  | some k =>
    exfalso
    have hperm := (walkGraph_perm_graphAt _ _ _).trans
      (graphAt_shard_perm ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).1
        ((threeColoring.attach parts).1.splitForced
          (threeColoring.attach parts).2 symmetry).2 b mask)
    have hchk' := checkGadget_perm_3col (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry) hperm
    rw [hchk] at hchk'
    have hmem := searchAux_complete threeColoring (threeColoring.attach parts).1
      (anchorsOf parts.length (threeColoring.attach parts).1)
      (gadgetRows threeColoring symmetry) (threeColoring_kill _ _ _) _ _
      { total := 2 ^ (shardSplit
          ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 symmetry).1
          ((threeColoring.attach parts).1.splitForced (threeColoring.attach parts).2 symmetry).2
          (2 ^ b) (mask % 2 ^ Nat.min b
            ((threeColoring.attach parts).1.splitForced
              (threeColoring.attach parts).2 symmetry).2.length)).2.length }
      _ k hchk'
    rw [hfound] at hmem
    cases hmem

/-- P4 corollary for a sharded symmetric sweep: if every shard of a 2^b-way
    split reports nothing, the raw eight-row table rejects every enumerated
    symmetric candidate of the slice. -/
theorem searchSlice_sharded_symmetric_covers_raw (parts : List Nat)
    (hparts : ∀ n ∈ parts, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) (b : Nat) (hb : 0 < b)
    (h : ∀ i, i < 2 ^ b →
      (searchSlice threeColoring parts true (2 ^ b) i).2.found = []) :
    ∀ g ∈ (threeColoring.attach parts).1.graphs (symmetry := true)
        (forced := (threeColoring.attach parts).2),
      gadgetK threeColoring parts g false = none := by
  intro g hg
  obtain ⟨hsub, hcl⟩ := graphs_symmetric_props (attach_legal parts hparts) rfl
    (threeColoring.attach parts).2 g hg
  rw [← gadgetK_s3_symmetry_reduction_threeColoring parts hparts hsub hcl]
  exact searchSlice_sharded_exhaustive_threeColoring_graphs parts true b hb h g hg

end Atlas
