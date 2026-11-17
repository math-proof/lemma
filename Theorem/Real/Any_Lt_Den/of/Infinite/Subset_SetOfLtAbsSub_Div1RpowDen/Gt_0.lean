module

public import Mathlib
public import Theorem.Real.FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0

public section

open Real


/--
[roth_ridout_exists_approx_den_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Real.Any_Lt_Den.of.Infinite.Subset_SetOfLtAbsSub_Div1RpowDen.Gt_0
  {α p : ℝ}
  (A : Set ℚ)
  (N : ℕ)
-- given
  (hp : 0 < p)
  (hA : A ⊆ {q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p})
  (hinf : A.Infinite) :
-- imply
  ∃ q ∈ A, N < q.den := by
-- proof
  by_contra! hbounded
  apply hinf
  refine (FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0 α p N hp).subset ?_
  intro q hq
  exact ⟨hA hq, hbounded q hq⟩


-- created on 2026-10-21
