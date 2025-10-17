import Lemma.Bool.HEq.of.Eq_Cast
import Lemma.Bool.EqCast.of.HEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
open Tensor Bool


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
  apply HEq.of.Eq_Cast ∘ Eq.of.EqDataS
  rw [Eq_Cast.of.HEq h]
  apply Cast_Data.eq.DataCast.of.Eq h_s


-- created on 2025-07-24
