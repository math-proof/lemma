/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions

@[expose] public section

namespace MetaMathlibExt.PollakPartialParking

theorem firstFree_not_mem (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : firstFree t occ a h ∉ occ :=
  Nat.find_spec (ray_free_exists t occ a h)

theorem firstFree_min (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) (j : ℕ)
    (hj : j < Nat.find (ray_free_exists t occ a h)) :
    a + (((j : ℕ)) : ZMod (t + 1)) ∈ occ := by
  by_contra hcon
  have hle := Nat.find_min' (ray_free_exists t occ a h) hcon
  omega

end MetaMathlibExt.PollakPartialParking
