import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Finset.MulSum.eq.Sum_Mul
import Lemma.Finset.Mul_Sum.eq.Sum_Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Fin.Sum.of.All_Eq
import Lemma.Finset.Sum_Sum
open Tensor Nat Finset Fin
set_option maxHeartbeats 20000000


/--
tensor version of Matrix.mul_assoc
-/
@[main]
private lemma main
  [NonUnitalSemiring α]
  {L : Tensor α [l, m]}
  {M : Tensor α [m, n]}
  {N : Tensor α [n, o]} :
-- imply
  (L @ M) @ N = L @ (M @ N) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  erw [GetDot.eq.Sum_MulGetS.fin (L @ M) N i j]
  erw [GetDot.eq.Sum_MulGetS.fin L (M @ N) i j]
  erw [GetDot.eq.Sum_MulGetS.fin L M i]
  erw [GetDot.eq.Sum_MulGetS.fin M N (j := j)]
  erw [MulSum.eq.Sum_Mul]
  erw [Mul_Sum.eq.Sum_Mul]
  erw [Sum_Sum.comm]
  erw [MulMul.eq.Mul_Mul]
  apply @Fin.Sum.of.All_Eq
  intro k
  apply @Fin.Sum.of.All_Eq
  intro ι
  apply MulMul.eq.Mul_Mul


-- created on 2025-05-03
-- updated on 2025-07-19
