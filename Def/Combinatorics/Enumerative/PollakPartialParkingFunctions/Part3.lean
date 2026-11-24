module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- Spot taken by car `n`. -/
noncomputable def parkAssign (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) : ZMod (t + 1) :=
  firstFree t (parkOcc s t g hst n) (g ⟨n, h⟩)
    (lt_of_le_of_lt (card_parkOcc_le s t g hst n) (by omega))

end MetaMathlibExt.PollakPartialParking
