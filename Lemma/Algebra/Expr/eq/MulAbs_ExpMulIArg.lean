import Lemma.Complex.Expr.eq.MulAbs_ExpMulIArg
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = ‖z‖ * (I * arg z).exp :=
-- proof
  Expr.eq.MulAbs_ExpMulIArg


-- created on 2018-07-26
-- updated on 2026-08-20
