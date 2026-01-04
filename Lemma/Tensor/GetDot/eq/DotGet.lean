import Lemma.List.Eq_Nil.is.EqLength_0
import Lemma.Nat.Eq.of.Ge.Le
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import stdlib.SEq
import sympy.tensor.tensor
open Tensor List Nat


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length > 0)
  (h_n : s'.length < s.length ∨ (s'.length = s.length ∧ n' ≥ n))
  (X : Tensor α (n :: s))
  (Y : Tensor α (n' :: s'))
  (i : Fin n) :
-- imply
  have h_i : i < (X @ Y).length := by
    if h_s' : s'.length > 0 then
      obtain h_n | h_n := h_n <;>
      .
        rw [Length.eq.Get_0.of.GtLength_0] <;>
        ·
          simp [matmul_shape, broadcast_shape]
          grind
    else
      rw [Length.eq.Get_0.of.GtLength_0] <;>
      .
        simp [matmul_shape, broadcast_shape]
        grind
  (X @ Y)[i]'(h_i) ≃ X[i] @ Y := by
-- proof
  sorry


-- created on 2026-01-04
