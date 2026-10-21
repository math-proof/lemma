import Mathlib
import sympy.Basic
import Lemma.Real.FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0
open Real


/--
[roth_exists_approx_den_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
