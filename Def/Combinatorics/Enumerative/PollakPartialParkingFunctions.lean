/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions

@[expose] public section

namespace MetaMathlibExt.PollakPartialParking

/-- First free spot clockwise from `a`: deterministic choice. -/
noncomputable def firstFree (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : ZMod (t + 1) :=
  a + ((((Nat.find (ray_free_exists t occ a h)) : ℕ)) : ZMod (t + 1))

end MetaMathlibExt.PollakPartialParking
