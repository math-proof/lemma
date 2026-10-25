/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part2


namespace MetaMathlibExt.PollakPartialParking

/-- Occupied spots after the first `n` cars park on the circle. Carries the
cardinality invariant. -/
noncomputable def parkOccAux (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    (n : ℕ) → { occ : Finset (ZMod (t + 1)) // occ.card ≤ n }
  | 0 => ⟨∅, by simp⟩
  | n + 1 =>
    if h : n < s then
      let occ := parkOccAux s t g hst n
      have hle : occ.val.card ≤ n := occ.property
      have hc : occ.val.card < t + 1 := by omega
      ⟨insert (firstFree t occ.val (g ⟨n, h⟩) hc) occ.val,
        by
          have hci :=
            Finset.card_insert_le (firstFree t occ.val (g ⟨n, h⟩) hc) occ.val
          omega⟩
    else
      ⟨(parkOccAux s t g hst n).val,
        le_trans (parkOccAux s t g hst n).property (Nat.le_succ n)⟩

/-- Occupied spots after the first `n` cars park on the circle. -/
noncomputable def parkOcc (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) : Finset (ZMod (t + 1)) :=
  (parkOccAux s t g hst n).val

end MetaMathlibExt.PollakPartialParking
