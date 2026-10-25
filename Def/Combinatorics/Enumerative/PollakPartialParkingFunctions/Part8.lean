/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part8


namespace MetaMathlibExt.PollakPartialParking

/-- The parking assignment extracted from a successful run. -/
noncomputable def linAssign (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) : Fin s → Fin t :=
  fun j => (linTake_some_of_success s t f hsucc j.val j.isLt).choose

end MetaMathlibExt.PollakPartialParking
