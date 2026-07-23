import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.SumStack.as.SumStack_Cast.of.Eq
import Lemma.Tensor.SumStack.of.All_Eq
open Bool Tensor


@[main]
private lemma main
  [AddMonoid α]
  {X : Fin m → Tensor α s}
  {Y : Fin m → Tensor α s'}
-- given
  (h_s : s = s')
  (h : ∀ i : Fin m, X i ≃ Y i) :
-- imply
  ∑ i < m, X i ≃ ∑ i < m, Y i := by
-- proof
  have h : ∀ i : Fin m, cast (congrArg (Tensor α) h_s) (X i) = Y i := by
    intro i
    apply EqCast.of.SEq
    apply h i
  have h := SumStack.of.All_Eq h
  rw [← h]
  apply SumStack.as.SumStack_Cast.of.Eq h_s


-- created on 2026-07-23
