import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PollakPartialParkingFunctions
open MetaMathlibExt.PollakPartialParking


/--
[pollak_partial_parking_functions_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean)
-/
@[path]
private lemma pollak_partial_parking_functions_card_eq
  {s t : ℕ}
-- given
  (hs : 0 < s)
  (hst : s ≤ t) :
-- imply
  Nat.card {f : Fin s → Fin t // IsPartialParkingFunction s t f} =
    (t + 1 - s) * (t + 1) ^ (s - 1) := by
-- proof
  apply MetaMathlibExt.PollakPartialParking.pollak_partial_parking_functions_card s t hs hst


-- created on 2026-10-20
