/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part7


namespace MetaMathlibExt.PollakPartialParking

/-- Spot taken by car `n`, if the process got that far and found one. -/
noncomputable def linTake (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (h : n < s) :
    Option (Fin t) :=
  match linOccAux s t f n with
  | none => none
  | some occ => linFirstFree t occ.val (f ⟨n, h⟩).val

end MetaMathlibExt.PollakPartialParking
