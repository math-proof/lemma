import Lemma.Rat.EqDiv_Div.of.Ne_0
open Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.EqDiv.is.Eq\_Div.of.Ne\_0 |
| comm | Rat.Eq\_Div.is.EqDiv.of.Ne\_0 |
| mp   | Rat.Eq\_Div.of.EqDiv.Ne\_0 |
| mpr  | Rat.EqDiv.of.Eq\_Div.Ne\_0 |
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
