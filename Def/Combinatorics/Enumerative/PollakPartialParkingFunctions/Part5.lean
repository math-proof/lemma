module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- First free spot at or after `a` in the linear lot, if any. -/
noncomputable def linFirstFree (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) :
    Option (Fin t) :=
  if h : (Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).Nonempty then
    some ((Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h)
  else none

end MetaMathlibExt.PollakPartialParking
