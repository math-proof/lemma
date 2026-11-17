module

public import Mathlib
public import Theorem.Real.FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0

public section

open Real


/--
[roth_exists_approx_den_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Real.Any_LtAbsSub_Div1RpowDenAndLt_Den.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0
  {α p : ℝ}
  (N : ℕ)
-- given
  (hp : 0 < p)
  (hinf : Set.Infinite {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p}) :
-- imply
  ∃ q : ℚ, |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p ∧ N < q.den := by
-- proof
  by_contra! hbounded
  apply hinf
  refine (FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0 α p N hp).subset ?_
  intro q hq
  exact ⟨hq, hbounded q hq⟩


-- created on 2026-10-21
