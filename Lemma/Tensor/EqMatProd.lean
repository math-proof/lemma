import Lemma.Tensor.EqDotEye
import Lemma.Tensor.MatProd.eq.DotMatProd
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
  {m : ℕ}
  (a : Tensor α [m, m]) :
-- imply
  matProd 1 (fun _ : Fin 1 => a) = a := by
-- proof
  apply Eq.trans (MatProd.eq.DotMatProd (f := fun _ : Fin 1 => a))
  simp only [matProd]
  apply EqDotEye


-- created on 2026-09-10
