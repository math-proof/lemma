import Lemma.Complex.Arg.eq.Ite__Ite_Arccos
import Lemma.Algebra.AbsAdd_MulI.eq.SqrtAddSquareS
import Lemma.Algebra.EqAdd_MulI_0.eq.AndEqS_0
open Algebra Complex


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
  have h := Arg.eq.Ite__Ite_Arccos (z := x + I * y)
  rw [AbsAdd_MulI.eq.SqrtAddSquareS (x := x) (y := y)] at h
  have h_Eq : (↑x + I * ↑y).re = x := by
    simp
  rw [h_Eq] at h
  have h_Eq : (↑x + I * ↑y).im = y := by
    simp
  rw [h_Eq] at h
  simp [EqAdd_MulI_0.eq.AndEqS_0 (x := x) (y := y)] at h
  exact h


-- created on 2025-01-05
