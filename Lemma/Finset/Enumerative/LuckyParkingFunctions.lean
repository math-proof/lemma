import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.LuckyParkingFunctions
open MetaMathlibExt


/--
[expected_lucky_spots_weakly_increasing_parking_functions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma expected_lucky_spots_weakly_increasing_parking_functions_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  let parkingFunctions := by
-- proof
  apply MetaMathlibExt.expected_lucky_spots_weakly_increasing_parking_functions n hn


-- created on 2026-10-20
