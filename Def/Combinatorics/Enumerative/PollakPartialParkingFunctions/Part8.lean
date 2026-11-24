module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- The parking assignment extracted from a successful run. -/
noncomputable def linAssign (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) : Fin s → Fin t :=
  fun j => (linTake_some_of_success s t f hsucc j.val j.isLt).choose

end MetaMathlibExt.PollakPartialParking
