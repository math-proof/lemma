import Lemma.Tensor.EqMatProd
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
  {m : ℕ}
  (f : Fin 2 → Tensor α [m, m]) :
-- imply
  matProd 2 f = (f (0 : Fin 2)) @ f 1 := by
-- proof
  apply MatProd.eq.DotMatProd.trans
  have h : matProd 1 (fun i : Fin 1 => f i.castSucc) = f 0 := by
    have hfun : (fun i : Fin 1 => f i.castSucc) = fun _ : Fin 1 => f 0 := by
      funext i
      fin_cases i
      simp
    rw [hfun]
    exact EqMatProd (f (0 : Fin 2))
  rw [h]
  rfl


-- created on 2020-11-16
