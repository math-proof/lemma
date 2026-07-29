import Lemma.Rat.EqDiv_Div.of.Ne_0
open Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.EqDiv.is.Eq_Div.of.Ne_0 |
| comm | Rat.Eq_Div.is.EqDiv.of.Ne_0 |
| mp   | Rat.Eq_Div.of.EqDiv.Ne_0 |
| mpr  | Rat.EqDiv.of.Eq_Div.Ne_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  [CommGroupWithZero α]
  {x y k : α}
-- given
  (h_y : y ≠ 0) :
-- imply
  y / x = k ↔ x = y / k := by
-- proof
  constructor <;>
    intro h
  .
    rw [← h]
    rw [EqDiv_Div.of.Ne_0 h_y]
  .
    rw [h]
    rw [EqDiv_Div.of.Ne_0 h_y]


-- created on 2025-12-20
