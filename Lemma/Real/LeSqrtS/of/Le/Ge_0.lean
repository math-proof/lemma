import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Real.EqSqrt_0.is.Le_0
import Lemma.Real.GeSqrt_0
import Lemma.Real.Le_Sqrt.is.LeSquare.of.Ge_0.Ge_0
open Real


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : y ≥ 0)
  (h_le : x ≤ y) :
-- imply
  √x ≤ √y := by
-- proof
  obtain hx | hx := le_total 0 x
  ·
    apply Le_Sqrt.of.LeSquare.Ge_0.Ge_0 (GeSqrt_0 (x := x)) h₀
    rwa [EqSquareSqrt.of.Ge_0 hx]
  ·
    rw [EqSqrt_0.of.Le_0 hx]
    exact GeSqrt_0 (x := y)


-- created on 2018-07-07
