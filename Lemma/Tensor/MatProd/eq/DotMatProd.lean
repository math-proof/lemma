import sympy.concrete.products


@[main]
private lemma main
  [Mul α] [AddMonoidWithOne α] [CharZero α]
  {m n : ℕ}
  {f : Fin (n + 1) → Tensor α [m, m]} :
-- imply
  Tensor.matProd (n + 1) f = (Tensor.matProd n fun i => f i.castSucc) @ (f (Fin.last n)) :=
-- proof
  rfl


-- created on 2020-08-29
-- updated on 2026-09-07
