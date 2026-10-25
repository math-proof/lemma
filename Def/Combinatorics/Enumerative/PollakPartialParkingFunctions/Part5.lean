/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part5


namespace MetaMathlibExt.PollakPartialParking

/-- First free spot at or after `a` in the linear lot, if any. -/
noncomputable def linFirstFree (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) :
    Option (Fin t) :=
  if h : (Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).Nonempty then
    some ((Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h)
  else none

end MetaMathlibExt.PollakPartialParking
