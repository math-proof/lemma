import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Algebra.MulSum.eq.Sum_Mul
import Lemma.Algebra.Mul_Sum.eq.Sum_Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Algebra.EqSumS
open Tensor Algebra Nat
set_option maxHeartbeats 1000000


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
  apply Eq.of.All_EqGetS (m := l)
  intro i
  apply Eq.of.All_EqGetS (m := o)
  intro j
  have := GetDot.eq.Sum_MulGetS (L @ M) N i j
  simp_all
  have := GetDot.eq.Sum_MulGetS L (M @ N) i j
  simp_all
  have := GetDot.eq.Sum_MulGetS L M i
  simp_all
  have := GetDot.eq.Sum_MulGetS M N (j := j)
  simp_all
  have : ∀ k : Fin n, (∑ ι : Fin m, L[i][ι] * M[ι][k]) * N[k][j] = ∑ ι : Fin m, L[i][ι] * M[ι][k] * N[k][j] := by
    simp [MulSum.eq.Sum_Mul]
  simp_all
  have : ∀ k : Fin m, L[i][k] * ∑ ι : Fin n, M[k][ι] * N[ι][j] = ∑ ι : Fin n, L[i][k] * (M[k][ι] * N[ι][j]) := by
    simp [Mul_Sum.eq.Sum_Mul]
  simp_all
  have : ∀ k : Fin m, ∑ ι : Fin n, L[i][k] * (M[k][ι] * N[ι][j]) = ∑ ι : Fin n, L[i][k] * M[k][ι] * N[ι][j] := by
    simp [MulMul.eq.Mul_Mul]
  simp_all
  apply EqSumS.comm


-- created on 2025-05-03
-- updated on 2025-07-19
