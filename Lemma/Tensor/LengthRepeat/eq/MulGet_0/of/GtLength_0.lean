import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
import Lemma.Algebra.Mul
open Tensor Algebra


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (X.repeat n ⟨0, h⟩).length = s[0] * n := by
-- proof
  rw [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  apply Mul.comm


-- created on 2025-07-10
-- updated on 2025-07-12
