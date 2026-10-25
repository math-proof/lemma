/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions


namespace MetaMathlibExt.PollakPartialParking

/-- First free spot clockwise from `a`: deterministic choice. -/
noncomputable def firstFree (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : ZMod (t + 1) :=
  a + ((((Nat.find (ray_free_exists t occ a h)) : ℕ)) : ZMod (t + 1))

end MetaMathlibExt.PollakPartialParking
