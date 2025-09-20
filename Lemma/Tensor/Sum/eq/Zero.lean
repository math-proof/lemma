import sympy.tensor.tensor
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Algebra.Eq.of.All_EqGetS
import Lemma.Algebra.Get.eq.Zero.of.Lt
import Lemma.Algebra.Sum.eq.Zero
open Tensor Algebra


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (0 :: s)) :
-- imply
  X.sum 0 = 0 := by
-- proof
  simp [Tensor.sum]
  apply Eq.of.EqDataS
  have h_zero : Tensor.data (0 : Tensor α ((0 :: s).eraseIdx 0)) = 0 := by
    rfl
  simp [h_zero]
  apply Eq.of.All_EqGetS
  intro i
  have h_i : i < ((0 :: s).eraseIdx 0).prod := by
    simp
  simp [Get.eq.Zero.of.Lt h_i]
  rw [Sum.eq.Zero]


-- created on 2025-09-04
