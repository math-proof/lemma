import Mathlib
import sympy.Basic
import Lemma.Set.FiniteSetOfLeAbsQAndLeDen
import Lemma.Real.Abs.le.AddAbs1.of.LtAbsSub_Div1RpowDen.Gt_0
open Set Real


/--
[roth_finite_approximants_of_den_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
