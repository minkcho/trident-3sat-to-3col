import atlas.ProofsDecide

/-!
  Build-time re-runs of the symmetric sweeps that Theorem 16 needs beyond
  `ProofsDecide`: every orbit composition with four, five or six auxiliary
  vertices that contains a size-3 or a size-6 orbit, except `[3, 3]`
  (`trident_slice_found`). Each sweep returns no valid gadget.

  Trust note: these are `native_decide`, like `sym_empty_111` and
  `trident_slice_found` in `ProofsDecide`. The kernel evaluator is not
  practical beyond about 2^13 candidates on this engine. The candidate
  counts are 2^13 ([1, 3]), 2^14 ([2, 3]), 2^19 ([1, 1, 3]), 2^12 ([6]),
  2^20 ([1, 2, 3]) and 2^26 ([1, 1, 1, 3]).
-/

namespace Atlas

theorem sym_empty_13 :
    (searchSlice threeColoring [1, 3] true).2.found = [] := by
  native_decide

theorem sym_empty_23 :
    (searchSlice threeColoring [2, 3] true).2.found = [] := by
  native_decide

theorem sym_empty_113 :
    (searchSlice threeColoring [1, 1, 3] true).2.found = [] := by
  native_decide

theorem sym_empty_6 :
    (searchSlice threeColoring [6] true).2.found = [] := by
  native_decide

theorem sym_empty_123 :
    (searchSlice threeColoring [1, 2, 3] true).2.found = [] := by
  native_decide

theorem sym_empty_1113 :
    (searchSlice threeColoring [1, 1, 1, 3] true).2.found = [] := by
  native_decide

end Atlas
