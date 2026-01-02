import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.PermuteMul.eq.MulPermuteS__Neg.of.GtLength_Add
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
open Tensor Bool


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (d : Fin s.length) :
-- imply
  (A * B).permute d (-d) = A.permute d (-d) * B.permute d (-d) := by
-- proof
  have h_AB := PermuteMul.eq.MulPermuteS__Neg.of.GtLength_Add (i := 0) (d := d) (A := A) (B := B) (by grind)
  have h_A := SEqPermuteS.of.SEq.Eq.Eq.GtLength (i := 0 + d) (i' := d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := A)
  have h_B := SEqPermuteS.of.SEq.Eq.Eq.GtLength (i := 0 + d) (i' := d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := B)
  have h_A_mul_B := SEqMulS.of.SEq.SEq h_A h_B
  rw [← h_AB] at h_A_mul_B
  apply Eq.of.SEq
  symm
  apply h_A_mul_B.symm.trans
  apply SEqPermuteS.of.SEq.Eq.Eq.GtLength
  .
    simp
  .
    rfl
  .
    rfl



-- created on 2025-12-03
