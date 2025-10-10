import sympy.tensor.Basic
import stdlib.SEq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Tensor.RepeatCast.as.Repeat.of.Eq
open Bool Tensor


@[main]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  ((cast (congrArg (Tensor α) h) X).repeat n ⟨d, by simp [← h]⟩) = cast (by simp [h]) (X.repeat n d) := by
-- proof
  apply Eq_Cast.of.SEq.Eq
  ·
    simp [h]
  ·
    apply RepeatCast.as.Repeat.of.Eq h


-- created on 2025-10-10
