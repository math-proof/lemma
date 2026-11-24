module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

theorem lift_restrict (s t : ℕ) (g : Fin s → ZMod (t + 1))
    (h : ∀ i, g i ≠ extra t) :
    lift s t (restrict s t g h) = g := by
  have : NeZero (t + 1) := ⟨by omega⟩
  funext i
  change (((g i).val : ℕ) : ZMod (t + 1)) = g i
  have h2 := ZMod.natCast_val (R := ZMod (t + 1)) (g i)
  rwa [ZMod.cast_id] at h2

theorem restrict_lift (s t : ℕ) (f : Fin s → Fin t)
    (h : ∀ i, lift s t f i ≠ extra t) :
    restrict s t (lift s t f) h = f := by
  funext i
  apply Fin.ext
  change (lift s t f i).val = (f i).val
  rw [show lift s t f i = emb t (f i) from rfl]
  exact emb_val t (f i)

end MetaMathlibExt.PollakPartialParking
