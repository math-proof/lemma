import Mathlib
import sympy.Basic
import Lemma.Real.LiouvilleWith.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0.Irrational
open Real


/--
[roth_finite_of_not_liouvilleWith](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α p : ℝ}
-- given
  (hα : Irrational α)
  (hp : 0 < p)
  (hnot : ¬LiouvilleWith p α) :
-- imply
  Set.Finite {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p} := by
-- proof
  by_contra hinf
  exact hnot (LiouvilleWith.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0.Irrational hα hp hinf)


-- created on 2026-10-21
