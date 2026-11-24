module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- Spot taken by car `n`, if the process got that far and found one. -/
noncomputable def linTake (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (h : n < s) :
    Option (Fin t) :=
  match linOccAux s t f n with
  | none => none
  | some occ => linFirstFree t occ.val (f ⟨n, h⟩).val

end MetaMathlibExt.PollakPartialParking
