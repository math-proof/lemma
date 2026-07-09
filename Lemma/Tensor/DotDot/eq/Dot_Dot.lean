import Lemma.Fin.Sum.of.All_Eq
import Lemma.Finset.Sum_Sum
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DotDot.eq.Sum_Sum_MulMul
import Lemma.Tensor.Dot_Dot.eq.Sum_Sum_Mul_Mul
import Lemma.Tensor.Eq.is.All_EqGetS
open Fin Finset Nat Tensor


/--
tensor version of Matrix.mul_assoc
-/
@[main]
private lemma main
  [NonUnitalSemiring α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o]) :
-- imply
  (L @ M) @ N = L @ (M @ N) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (DotDot.eq.Sum_Sum_MulMul L M N i j).trans
  symm
  apply (Dot_Dot.eq.Sum_Sum_Mul_Mul L M N i j).trans
  apply @Fin.Sum.of.All_Eq
  intro k
  apply @Fin.Sum.of.All_Eq
  intro ι
  apply Mul_Mul.eq.MulMul


-- created on 2025-05-03
-- updated on 2026-07-09
