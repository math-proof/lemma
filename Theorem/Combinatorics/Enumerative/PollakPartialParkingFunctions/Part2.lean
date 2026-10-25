/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions


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
