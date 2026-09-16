import Lemma.Tensor.EqT0'0
import Lemma.Tensor.EqUnsqueeze0'0
import Lemma.Tensor.Repeat0.eq.Zero
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqSum0_0
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
open Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {batch_size : List ℕ} {m k n : ℕ}
-- given
  (X : Tensor α (batch_size ++ [m, k])) :
-- imply
  X.bmm (0 : Tensor α (batch_size ++ [k, n])) = 0 := by
-- proof
  simp only [Tensor.bmm, Tensor.EqT0'0]
  rw [Tensor.EqCast_0'0.of.Eq (by simp [List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength])]
  simp only [EqUnsqueeze0'0]
  rw [Tensor.EqCast_0'0.of.Eq (by simp [List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength])]
  simp only [Tensor.Repeat0.eq.Zero]
  rw [Tensor.EqCast_0'0.of.Eq (by simp)]
  simp only [Nat.EqMul_0'0, EqSum0_0]
  rw [Tensor.EqCast_0'0.of.Eq (by simp [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength])]


-- created on 2026-09-16
