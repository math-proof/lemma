import Lemma.Tensor.Abs.eq.IteLe
import Lemma.Tensor.ItemNeg.eq.NegItem
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.ItemAbs.eq.AbsItem |
| comm | Tensor.AbsItem.eq.ItemAbs |
-/
@[main, comm]
private lemma main
  [AddGroup α] [LinearOrder α]
-- given
  (a : Tensor α []) :
-- imply
  |a|.item = |a.item| := by
-- proof
  rw [Abs.eq.IteLe, abs_eq_max_neg, max_def]
  split_ifs <;> simp [ItemNeg.eq.NegItem]


-- created on 2026-09-07
