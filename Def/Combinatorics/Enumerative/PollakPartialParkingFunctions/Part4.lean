/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part4


namespace MetaMathlibExt.PollakPartialParking

/-- Empty spots after circular parking. -/
noncomputable def parkEmpty (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    Finset (ZMod (t + 1)) :=
  Finset.univ \ parkOcc s t g hst s

end MetaMathlibExt.PollakPartialParking
