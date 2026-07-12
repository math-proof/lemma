import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqAppend0S0
import Lemma.Vector.SEq0S.of.Eq
open Bool Tensor Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n m : ℕ)
  (s : List ℕ) :
-- imply
  (0 : Tensor α (n :: s)) ++ (0 : Tensor α (m :: s)) = (0 : Tensor α ((n + m) :: s)) := by
-- proof
  apply Eq.of.EqDataS
  simp [EqData0'0]
  rw [DataAppend.eq.Cast_AppendDataS]
  apply EqCast.of.SEq.Eq (by grind)
  simp [EqData0'0]
  erw [EqAppend0S0]
  apply SEq0S.of.Eq
  grind


-- created on 2026-07-12
