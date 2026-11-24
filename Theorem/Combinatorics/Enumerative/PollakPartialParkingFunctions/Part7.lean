module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

theorem linOccAux_zero (s t : ℕ) (f : Fin s → Fin t) :
    linOccAux s t f 0 = some ⟨∅, by simp⟩ := rfl

theorem linOccAux_succ_some (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) (h : n < s) (x : Fin t)
    (hff : linFirstFree t occ.val (f ⟨n, h⟩).val = some x) :
    linOccAux s t f (n + 1) = some ⟨insert x occ.val, by
      have _hle : occ.val.card ≤ n := occ.property
      have hci := Finset.card_insert_le x occ.val
      omega⟩ := by
  simp only [linOccAux, hm, h, hff, dite_true]

theorem linOccAux_succ_none_take (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) (h : n < s)
    (hff : linFirstFree t occ.val (f ⟨n, h⟩).val = none) :
    linOccAux s t f (n + 1) = none := by
  simp only [linOccAux, hm, h, hff, dite_true]

theorem linOccAux_succ_failed (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (hm : linOccAux s t f n = none) :
    linOccAux s t f (n + 1) = none := by
  simp only [linOccAux, hm]

end MetaMathlibExt.PollakPartialParking
