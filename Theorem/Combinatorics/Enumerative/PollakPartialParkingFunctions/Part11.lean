/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part10


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
