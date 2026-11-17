module

public import Mathlib
public import Theorem.Real.LiouvilleWith.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0.Irrational

public section

open Real


/--
[roth_finite_of_not_liouvilleWith](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Real.FiniteSetOfLtAbsSub_Div1RpowDen.of.NotLiouvilleWith.Gt_0.Irrational
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
