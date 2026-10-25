/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part3


namespace MetaMathlibExt.PollakPartialParking

/-- Spot taken by car `n`. -/
noncomputable def parkAssign (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) : ZMod (t + 1) :=
  firstFree t (parkOcc s t g hst n) (g ⟨n, h⟩)
    (lt_of_le_of_lt (card_parkOcc_le s t g hst n) (by omega))

end MetaMathlibExt.PollakPartialParking
