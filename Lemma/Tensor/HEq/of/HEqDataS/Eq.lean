import Lemma.Logic.HEq.of.Eq_Cast
import Lemma.Logic.EqCast.of.HEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Tensor.Cast_Data.eq.DataCast.of.Eq
open Logic Tensor


@[main]
private lemma main
  {s s' : List ℕ}
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s = s')
  (h : HEq A.data B.data) :
-- imply
  HEq A B := by
-- proof
  apply HEq.of.Eq_Cast
  apply Eq.of.EqDataS
  rw [Eq_Cast.of.HEq h]
  apply Cast_Data.eq.DataCast.of.Eq h_s.symm B


-- created on 2025-07-24
