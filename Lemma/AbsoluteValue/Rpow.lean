import Mathlib
import sympy.Basic
import sympy.Analysis.AbsoluteValue.Rpow

/--
[rpow_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/AbsoluteValue/Rpow.lean)
-/
@[path]
private lemma rpow_apply_eq
  [Semiring R]
-- given
  (v : AbsoluteValue R ℝ) (c : ℝ) (hc₀ : 0 < c) (hc₁ : c ≤ 1) (x : R) :
-- imply
  v.rpow c hc₀ hc₁ x = v x ^ c := by
-- proof
  apply AbsoluteValue.rpow_apply


-- created on 2026-10-09
