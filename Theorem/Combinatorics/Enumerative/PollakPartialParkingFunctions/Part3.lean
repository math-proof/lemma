module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

theorem card_parkOcc_le (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) : (parkOcc s t g hst n).card ≤ n :=
  (parkOccAux s t g hst n).property

end MetaMathlibExt.PollakPartialParking
