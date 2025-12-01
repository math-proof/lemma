import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.TailPermute__Neg.eq.EraseIdx
import Lemma.Tensor.LengthPermute.eq.Get
import Lemma.Tensor.Select.as.GetPermute
open Bool List Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  have h := TailPermute__Neg.eq.EraseIdx d
  X.select d i = cast (congrArg (Tensor α) h) ((X.permute d (-d)).get ⟨i, by simp [LengthPermute.eq.Get]⟩) := by
-- proof
  intro h
  apply Eq_Cast.of.SEq.Eq h
  apply Select.as.GetPermute


-- created on 2025-12-01
