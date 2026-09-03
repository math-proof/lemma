import Lemma.Tensor.AppendHstackS.eq.Eye
import Lemma.Tensor.Cos0.eq.One
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.EqStack_0'0
import Lemma.Tensor.EqStack_1'1
import Lemma.Tensor.Sin0.eq.Zero
open Tensor


@[main]
private lemma main :
-- imply
  rotaryMatrix (0 : Tensor ℝ [d]) = Tensor.eye (d + d) := by
-- proof
  simp only [rotaryMatrix]
  rw [Cos0.eq.One, Sin0.eq.Zero]
  rw [EqStack_1'1 [d] d, EqStack_0'0 [d] d]
  rw [mul_one, mul_zero, neg_zero]
  exact AppendHstackS.eq.Eye d d


-- created on 2026-09-03
