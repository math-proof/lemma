module

public import Mathlib
public import Theorem.Set.FiniteSetOfLeAbsQAndLeDen
public import Theorem.Real.Abs.le.AddAbs1.of.LtAbsSub_Div1RpowDen.Gt_0

public section

open Set Real


/--
[roth_finite_approximants_of_den_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Real.FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0
  (α p : ℝ)
  (N : ℕ)
-- given
  (hp : 0 < p) :
-- imply
  Set.Finite {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p ∧ q.den ≤ N} := by
-- proof
  refine (FiniteSetOfLeAbsQAndLeDen (|α| + 1) N).subset ?_
  rintro q ⟨hq, hden⟩
  exact ⟨Abs.le.AddAbs1.of.LtAbsSub_Div1RpowDen.Gt_0 q hp hq, hden⟩


-- created on 2026-10-21
