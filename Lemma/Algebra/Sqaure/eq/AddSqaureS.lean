import Lemma.Algebra.Norm.eq.SqrtAddSqaureS
import Lemma.Algebra.AddSquareS.ge.Zero
import Lemma.Algebra.EqSquareSqrt.of.Ge_0
import Lemma.Logic.EqFunS.of.Eq
open Algebra Logic


@[main]
private lemma main
  {z : ℂ} :
-- imply
    ‖z‖² = (re z)² + (im z)² := by
-- proof
  have := Norm.eq.SqrtAddSqaureS (z := z)
  have h := EqFunS.of.Eq this (·²)
  have := AddSquareS.ge.Zero (a := re z) (b := im z)
  have := EqSquareSqrt.of.Ge_0 this
  exact this ▸ h


-- created on 2025-01-16
-- updated on 2025-05-10
