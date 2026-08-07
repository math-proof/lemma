import Lemma.Complex.Arg.eq.Ite_Arcsin_Ite_Sub_Arcsin
import Lemma.Real.AbsAdd_MulI.eq.SqrtAddSquareS
open Complex Real


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  arg (x + I * y) =
    if x ≥ 0 then
      arcsin (y / √(x² + y²))
    else if y ≥ 0 then
      π - arcsin (y / √(x² + y²))
    else
      -arcsin (y / √(x² + y²)) - π := by
-- proof
  have h := Arg.eq.Ite_Arcsin_Ite_Sub_Arcsin (z := x + I * y)
  rw [AbsAdd_MulI.eq.SqrtAddSquareS (x := x) (y := y)] at h
  simp at h
  exact h


-- created on 2018-07-24
