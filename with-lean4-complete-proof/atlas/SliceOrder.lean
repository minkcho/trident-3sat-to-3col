import atlas.Framework
/-!
  slice order: cheapest slice first for the sweep.

  Kept out of Framework.lean on purpose: the proof layer imports Framework,
  so any change there re-elaborates every Proofs* module (the raw-minimality
  re-runs alone take ~13 minutes), while the ordering is a pure scheduling
  concern of the sweep and the tests, which import this module instead.
  Ported verbatim from atlas-ext2 (commit 7b60850).
-/

namespace Atlas

/-- The exponent of a slice's candidate count: the number of free switches
    left after the problem's framework is attached and its forced orbits
    split off (the slice cost is 2^this). Aggregated compositions compress
    more, so their exponents are smaller. -/
def sliceCost (P : Problem) (parts : List Nat) (symmetry : Bool := true) : Nat :=
  let (U, forced) := P.attach parts
  (U.splitForced forced symmetry).2.length

/-- Cheapest slice first: order a budget's slices by ascending free-switch
    count, so the most aggregated (most symmetric, smallest 2^K) slices run
    before the singleton-heavy ones. A pure reordering -- the found set and
    the accounting of a sweep are order-independent. -/
def orderSlices (P : Problem) (slices : List (List Nat))
    (symmetry : Bool := true) : List (List Nat) :=
  (((slices.map fun parts => (sliceCost P parts symmetry, parts)).toArray.qsort
    fun a b => a.1 < b.1).toList).map (·.2)

end Atlas
