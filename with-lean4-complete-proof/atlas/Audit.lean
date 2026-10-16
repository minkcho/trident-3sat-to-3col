import atlas.Atlas
/-!
  audit: independently computed expectations for the enumeration layers.

  Everything here deliberately shares no code with the generators it checks.
  `partitionCount` counts what `compositions` enumerates, by the same
  recursion (budget x allowed-suffix) counted rather than built -- so it
  guards the list construction, not the recursion ([opus5.5 review]
  corrected; `compositionsAux_length` proves the two agree); `allTuples` is
  the ordered brute force whose sorted deduplication must equal
  `compositions`; `invariantUnder` is the definitional S3-invariance test
  whose filter over the raw walk must equal the symmetric generator. A
  mismatch anywhere is an enumeration bug, never a modeling choice. The
  sweep consumes these counts as a runtime guard, the tests as assertions.
-/

namespace Atlas

-- (in this project `legalSizes` lives in Atlas.lean: the enumeration is
-- built on it and Proofs.lean proves its properties, so the audit DP and
-- the generator legitimately share the preprocessing here)

/-- Number of non-decreasing lists over `allowed` (as a suffix set) summing
    to the budget: use the head size again or drop to the tail. -/
def countParts : Nat → List Nat → Nat
  | 0, _ => 1
  | _ + 1, [] => 0
  | k + 1, s :: rest =>
    (if h : 1 ≤ s ∧ s ≤ k + 1 then countParts (k + 1 - s) (s :: rest) else 0) +
    countParts (k + 1) rest
termination_by k allowed => k + allowed.length
decreasing_by all_goals (simp only [List.length_cons]; omega)

/-- How many orbit-type compositions of `k` there are -- the independent
    count that `(compositions k sizes).length` must match. -/
def partitionCount (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) : Nat :=
  countParts k (legalSizes sizes)

/-- How many of them contain at least one part of size `s` (complement
    counting: all minus those built without `s`). -/
def partitionCountWith (k : Nat) (sizes : List Nat) (s : Nat) : Nat :=
  partitionCount k sizes - partitionCount k (sizes.filter (· != s))

/-- Every ordered tuple over the legal sizes summing to `k`: the brute-force
    oracle behind the set-equality check on `compositions`. -/
def tuplesAux (ss : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => ss.flatMap fun s =>
    if h : 1 ≤ s ∧ s ≤ k + 1 then (tuplesAux ss (k + 1 - s)).map (s :: ·)
    else []
termination_by k => k
decreasing_by omega

def allTuples (k : Nat) (sizes : List Nat := [1, 2, 3, 6]) : List (List Nat) :=
  tuplesAux (legalSizes sizes) k

/-- Definitional S3-invariance of an edge set: every group element maps it
    into itself (the action is a bijection, so into is onto). -/
def invariantUnder (U : Universe) (g : List Edge) : Bool :=
  perms.all fun s => g.all fun e => g.contains (U.actEdge s e)

end Atlas
