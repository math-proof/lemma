import Lemma.Tensor.EqDotEye
import Lemma.Tensor.MatProd.eq.DotMatProd
import Lemma.Tensor.SwapMatrix.eq.Eye
open Tensor


private lemma matProd_eye
  [Semiring α] [CharZero α]
  (n m : ℕ) :
  matProd n (fun _ : Fin n => eye (α := α) m) = eye m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [MatProd.eq.DotMatProd]
    rw [ih]
    apply EqDotEye


@[main]
private lemma main
  [Semiring α] [CharZero α]
  (n : ℕ) :
-- imply
  matProd n (fun i : Fin n => SwapMatrix n i i) = eye (α := α) n := by
-- proof
  have hfun : (fun i : Fin n => SwapMatrix n i i) = fun _ : Fin n => eye (α := α) n := by
    funext i
    exact SwapMatrix.eq.Eye n i
  rw [congrArg (fun f => matProd n f) hfun]
  exact matProd_eye n n


-- created on 2026-09-10
