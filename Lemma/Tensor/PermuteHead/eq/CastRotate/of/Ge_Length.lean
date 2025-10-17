import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.PermuteHead.as.Rotate.of.Ge_Length
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.Drop.eq.Nil.of.Ge_Length
open Bool Tensor List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : n ≥ s.length)
  (X : Tensor α s) :
-- imply
  have h : s.rotate 1 = ((s.take n).rotate 1 ++ s.drop n) := by
    rw [EqTake.of.Ge_Length h]
    simp [Drop.eq.Nil.of.Ge_Length h]
  X.permuteHead n = cast (congrArg (Tensor α) h) (X.rotate 1) := by
-- proof
  apply Eq_Cast.of.SEq
  apply PermuteHead.as.Rotate.of.Ge_Length h


-- created on 2025-10-17
