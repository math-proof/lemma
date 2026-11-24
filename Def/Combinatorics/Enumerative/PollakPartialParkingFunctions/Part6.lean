module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
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
