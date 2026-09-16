import sympy.matrices.expressions.matmul
import Lemma.Tensor.EqMatmul_0'0
import Lemma.Tensor.EqCast_0'0.of.Eq
import Lemma.Tensor.Reshape0.eq.Zero
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Append.of.Eq
import Lemma.List.ZipWith_Append.eq.AppendZipWithS
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
open Tensor


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {s s' : List ℕ} {m n k : ℕ}
-- given
  (X : Tensor α (s ++ [m, n])) :
-- imply
  X.tensordot (0 : Tensor α (s' ++ [n, k])) = 0 := by
-- proof
  unfold Tensor.tensordot
  split_ifs
  · simp (config := { zeta := true }) only []
    rw [Tensor.EqMatmul_0'0 _ (by
      rw [List.length_append, List.length_take]; omega)]
    rw [Tensor.EqCast_0'0.of.Eq (by
      simp [broadcast_shape]
      split_ifs with h_l h_u
      · grind
      · grind
      · simp
        rw [List.Append_Append.eq.AppendAppend]
        apply List.Append.of.Eq
        rw [List.ZipWith_Append.eq.AppendZipWithS]
        apply List.Append.of.Eq
        simp)]
  · simp (config := { zeta := true }) only []
    simp only [Tensor.Reshape0.eq.Zero]
    rw [Tensor.EqMatmul_0'0 _ (by
      rw [List.length_append, List.length_take]; omega)]
    rw [Tensor.EqCast_0'0.of.Eq (by
      simp [broadcast_shape]
      split_ifs with h_l h_u
      · grind
      · grind
      · simp
        rw [List.Append_Append.eq.AppendAppend]
        apply List.Append.of.Eq
        rw [List.ZipWith__Append.eq.AppendZipWithS]
        apply List.Append.of.Eq
        simp)]
  · rw [Tensor.EqMatmul_0'0 _ (by omega)]


-- created on 2026-09-16
