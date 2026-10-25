/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part9


namespace MetaMathlibExt.PollakPartialParking

/-- Embedding of linear spots into the circle. -/
def emb (t : ℕ) (x : Fin t) : ZMod (t + 1) := ((x.val : ℕ) : ZMod (t + 1))

/-- The extra spot on the circle. -/
def extra (t : ℕ) : ZMod (t + 1) := ((t : ℕ) : ZMod (t + 1))

/-- Lifting linear preferences to the circle. -/
def lift (s t : ℕ) (f : Fin s → Fin t) : Fin s → ZMod (t + 1) :=
  fun i => emb t (f i)

end MetaMathlibExt.PollakPartialParking
