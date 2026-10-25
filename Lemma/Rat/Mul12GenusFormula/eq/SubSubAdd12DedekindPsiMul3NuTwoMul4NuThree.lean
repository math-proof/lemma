import Mathlib
import sympy.Basic
import Lemma.ModularCurve.GenusNumerics
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_twelve_mul_genusFormula](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_twelve_mul_genusFormula.lean)
-/
@[path]
private lemma main
  {N : ℕ} :
-- imply
  12 * genusFormula N = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ)
    - 6 * (cuspCount N : ℚ) := by
-- proof
  unfold genusFormula
  ring


-- created on 2026-10-23
