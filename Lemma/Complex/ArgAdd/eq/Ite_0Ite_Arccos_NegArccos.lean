import Lemma.Complex.EqArg_Ite_0Ite_Arccos_NegArccos
import Lemma.Real.AbsAdd_MulI.eq.SqrtAddSquareS
import Lemma.Real.EqAdd_MulI_0.is.AndEqS_0
open Complex Real


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  arg (x + I * y) =
    if (x = 0 ∧ y = 0) then
      0
    else if y ≥ 0 then
      arccos (x / √(x² + y²))
    else
      -arccos (x / √(x² + y²)) := by
-- proof
  have h := EqArg_Ite_0Ite_Arccos_NegArccos (z := x + I * y)
  rw [AbsAdd_MulI.eq.SqrtAddSquareS (x := x) (y := y)] at h
  have h_Eq : (↑x + I * ↑y).re = x := by
    simp
  rw [h_Eq] at h
  have h_Eq : (↑x + I * ↑y).im = y := by
    simp
  rw [h_Eq] at h
  simp [EqAdd_MulI_0.is.AndEqS_0 (x := x) (y := y)] at h
  exact h


-- created on 2018-06-04
