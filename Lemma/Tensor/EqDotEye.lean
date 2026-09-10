import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
open Nat Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma mv
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n]) :
-- imply
  (Tensor.eye (α := α) n) @ x = x := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro j
  have h := GetDot.eq.Sum_MulGetS.mv (Tensor.eye (α := α) n) x j
  apply h.trans
  apply (Finset.sum_eq_single j ?_ ?_).trans ?_
  ·
    intro k _ hk
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) t * id (α := Tensor α []) (x[k] : Tensor α [])) (GetEye.eq.Delta.fin (α := α) j k)).trans
    simp [Delta.eq.Ite, Ne.symm hk]
    apply EqMul0_0.nat
  ·
    intro hj
    exact (hj (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor α [] => id (α := Tensor α []) t * id (α := Tensor α []) (x[j] : Tensor α [])) (GetEye.eq.Delta.fin (α := α) j j)).trans
    simp [Delta.eq.Ite]
    apply EqMul1.nat


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
    apply EqMul0_0.nat
  ·
    intro h
    apply (h (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) A[i][j]) (GetEye.eq.Delta.fin (α := α) i i)).trans
    simp [Delta.eq.Ite]
    apply EqMul1.nat


-- created on 2026-09-05
-- updated on 2026-09-10
