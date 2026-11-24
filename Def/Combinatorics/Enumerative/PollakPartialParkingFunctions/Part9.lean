module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- Embedding of linear spots into the circle. -/
def emb (t : ℕ) (x : Fin t) : ZMod (t + 1) := ((x.val : ℕ) : ZMod (t + 1))

/-- The extra spot on the circle. -/
def extra (t : ℕ) : ZMod (t + 1) := ((t : ℕ) : ZMod (t + 1))

/-- Lifting linear preferences to the circle. -/
def lift (s t : ℕ) (f : Fin s → Fin t) : Fin s → ZMod (t + 1) :=
  fun i => emb t (f i)

end MetaMathlibExt.PollakPartialParking
