module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- Empty spots after circular parking. -/
noncomputable def parkEmpty (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    Finset (ZMod (t + 1)) :=
  Finset.univ \ parkOcc s t g hst s

end MetaMathlibExt.PollakPartialParking
