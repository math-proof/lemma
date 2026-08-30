import Lemma.Complex.Expr.eq.AddRe_MulIIm
import Lemma.Real.AbsAdd_MulI.eq.SqrtAddSquareS
open Complex Real


@[main]
private lemma main
  {z : ℂ} :
-- imply
  ‖z‖ = √((re z)² + (im z)²) := by
-- proof
  conv_lhs => rw [Expr.eq.AddRe_MulIIm (z := z)]
  rw [AbsAdd_MulI.eq.SqrtAddSquareS]


-- created on 2018-06-12
