/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part6


namespace MetaMathlibExt.PollakPartialParking

/-- Occupied spots after the first `n` cars park in the linear lot, if all
succeeded. Carries the cardinality invariant; `none` on failure. -/
noncomputable def linOccAux (s t : ℕ) (f : Fin s → Fin t) :
    (n : ℕ) → Option { occ : Finset (Fin t) // occ.card ≤ n }
  | 0 => some ⟨∅, by simp⟩
  | n + 1 =>
    match linOccAux s t f n with
    | none => none
    | some occ =>
      if h : n < s then
        match linFirstFree t occ.val (f ⟨n, h⟩).val with
        | some x =>
          some ⟨insert x occ.val, by
            have hle : occ.val.card ≤ n := occ.property
            have hci := Finset.card_insert_le x occ.val
            omega⟩
        | none => none
      else some ⟨occ.val, le_trans occ.property (Nat.le_succ n)⟩

/-- Successful parking of all cars. -/
def LinSuccess (s t : ℕ) (f : Fin s → Fin t) : Prop :=
  (linOccAux s t f s).isSome

end MetaMathlibExt.PollakPartialParking
