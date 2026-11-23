import Lemma.Tensor.Mul
import Lemma.Tensor.Sub
open Tensor


@[path]
private lemma main
-- given
  (c s x0 x1 : Tensor ℝ []) :
-- imply
  Add.add (c * x0) (-s * x1) = x0 * c - x1 * s := by
-- proof
  rw [Tensor.Sub]
  simp only [Tensor.Mul]
  change Add.add (Mul.mul c x0) (Mul.mul (-s) x1) =
    Sub.sub (Mul.mul x0 c) (Mul.mul x1 s)
  apply Eq.trans _ (sub_eq_add_neg (Mul.mul x0 c) (Mul.mul x1 s)).symm
  congr 1
  ·
    apply _root_.mul_comm
  ·
    apply (neg_mul s x1).trans
    apply congrArg Neg.neg (_root_.mul_comm s x1)


-- created on 2026-09-17
-- updated on 2026-11-20
