import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.Periodic.LiYorke
open MathlibExt.Dynamics.Periodic.LiYorkeWanted


/--
[liYorke_period_three_implies_periods](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Periodic/LiYorke.lean)
-/
@[path]
private lemma liYorke_period_three_implies_periods_eq
  {f : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1}
-- given
  (hf : Continuous f)
  (h0 : ∃ x, Function.minimalPeriod f x = 3) :
-- imply
  ∀ (n : ℕ), 0 < n → ∃ y, Function.minimalPeriod f y = n := by
-- proof
  apply MathlibExt.Dynamics.Periodic.LiYorkeWanted.liYorke_period_three_implies_periods f hf h0


-- created on 2026-10-20
