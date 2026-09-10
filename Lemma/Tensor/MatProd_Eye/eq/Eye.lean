import Lemma.Tensor.EqDotEye
import Lemma.Tensor.MatProd.eq.DotMatProd
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
  (n m : ℕ) :
-- imply
  matProd n (fun _ : Fin n => eye (α := α) m) = eye m := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [MatProd.eq.DotMatProd]
    rw [ih]
    apply EqDotEye


-- created on 2026-09-10
