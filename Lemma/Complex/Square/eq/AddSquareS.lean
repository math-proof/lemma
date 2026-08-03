import Lemma.Complex.Norm.eq.SqrtAddSquareS
import Lemma.Int.AddSquareS.ge.Zero
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Bool.UFn.of.Eq
open Bool Complex Int Real


@[main]
private lemma main
  {z : ℂ} :
-- imply
    ‖z‖² = (re z)² + (im z)² := by
-- proof
  have := Norm.eq.SqrtAddSquareS (z := z)
  have h := UFn.of.Eq this (·²)
  have := AddSquareS.ge.Zero (a := re z) (b := im z)
  have := EqSquareSqrt.of.Ge_0 this
  exact this ▸ h


-- created on 2025-01-16
-- updated on 2025-05-10
