import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
open Nat Tensor


@[main]
private lemma vm
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n]) :
-- imply
  x @ Tensor.eye (α := α) n = x := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro j
  have h := GetDot.eq.Sum_MulGetS.une x (Tensor.eye (α := α) n) j
  apply h.trans
  apply (Finset.sum_eq_single j ?_ ?_).trans ?_
  ·
    intro k _ hk
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) (x[k] : Tensor α []) * id (α := Tensor α []) t) (GetEye.eq.Delta.fin (α := α) k j)).trans
    simp [Delta.eq.Ite, hk]
    apply Tensor.EqMul_0'0.nat
  ·
    intro hj
    exact (hj (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) (x[j] : Tensor α []) * id (α := Tensor α []) t) (GetEye.eq.Delta.fin (α := α) j j)).trans
    simp [Delta.eq.Ite]
    apply Tensor.EqMul_1.nat


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (A : Tensor α [m, n]) :
-- imply
  A @ Tensor.eye (α := α) n = A := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (GetDot.eq.Sum_MulGetS A (Tensor.eye (α := α) n) i j).trans
  apply (Finset.sum_eq_single j ?_ ?_).trans ?_
  ·
    intro k _ hk
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) A[i][k] * t) (GetEye.eq.Delta.fin (α := α) k j)).trans
    simp [Delta.eq.Ite, hk]
    apply EqMul_0'0.nat
  ·
    intro h
    apply (h (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) A[i][j] * t) (GetEye.eq.Delta.fin (α := α) j j)).trans
    simp [Delta.eq.Ite]
    apply EqMul_1.nat


-- created on 2026-09-05
-- updated on 2026-09-10
