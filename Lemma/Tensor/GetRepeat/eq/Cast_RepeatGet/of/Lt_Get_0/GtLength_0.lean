import Lemma.Bool.EqCast.of.SEq
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Tensor.GetRepeat.as.RepeatGet.of.Lt_Get_0.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
open Nat Tensor Bool


@[main, fin]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.tail.length) :
-- imply
  have h_d := d.isLt
  have : i < (X.repeat n ⟨d + 1, by apply LtAdd.of.Lt_Sub; simp_all⟩).length := by
    rwa [LengthRepeat.eq.Get_0.of.GtVal_0]
    simp
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.repeat n ⟨d + 1, by grind⟩)[i] = cast (by simp) (X[i].repeat n d) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetRepeat.as.RepeatGet.of.Lt_Get_0.GtLength_0 h_s h_i


-- created on 2026-01-13
