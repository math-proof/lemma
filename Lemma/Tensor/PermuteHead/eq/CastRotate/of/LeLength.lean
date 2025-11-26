import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.PermuteHead.as.Rotate.of.LeLength
import Lemma.List.EqTake.of.LeLength
import Lemma.List.Drop.eq.Nil.of.LeLength
open Bool Tensor List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length ≤ n)
  (X : Tensor α s) :
-- imply
  have h : s.rotate 1 = ((s.take n).rotate 1 ++ s.drop n) := by
    rw [EqTake.of.LeLength h]
    simp [Drop.eq.Nil.of.LeLength h]
  X.permuteHead n = cast (congrArg (Tensor α) h) (X.rotate 1) := by
-- proof
  apply Eq_Cast.of.SEq
  apply PermuteHead.as.Rotate.of.LeLength h


-- created on 2025-10-17
