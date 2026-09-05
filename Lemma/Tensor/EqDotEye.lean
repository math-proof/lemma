import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
import sympy.matrices.expressions.special
open Nat Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (A : Tensor α [m, n]) :
-- imply
  (Tensor.eye (α := α) m) @ A = A := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (GetDot.eq.Sum_MulGetS (Tensor.eye (α := α) m) A i j).trans
  apply (Finset.sum_eq_single i ?_ ?_).trans ?_
  ·
    intro k _ hk
    apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) A[k][j]) (GetEye.eq.Delta.fin (α := α) i k)).trans
    simp [Delta.eq.Ite, Ne.symm hk]
    apply Tensor.EqMul0_0.nat
  ·
    intro h
    apply (h (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) A[i][j]) (GetEye.eq.Delta.fin (α := α) i i)).trans
    simp [Delta.eq.Ite]
    apply Tensor.EqMul1.nat


-- created on 2026-09-05
