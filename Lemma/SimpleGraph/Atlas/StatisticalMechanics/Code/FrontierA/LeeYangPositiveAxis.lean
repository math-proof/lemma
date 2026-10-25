import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPositiveAxis
open Finset Polynomial StatMech StatMech.FrontierA


/--
[zeroFieldInteractionWeight_mul_pow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPositiveAxis.lean)
-/
@[path]
private lemma zeroFieldInteractionWeight_mul_pow_pos_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℝ}
  {s : ConfigSpace V}
-- given
  (hz : 0 < z) :
-- imply
  0 < zeroFieldInteractionWeight G beta s * z ^ minusSpinCount s := by
-- proof
  apply StatMech.FrontierA.zeroFieldInteractionWeight_mul_pow_pos beta hz s

/--
[eval_leeYangPolynomial_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPositiveAxis.lean)
-/
@[path]
private lemma eval_leeYangPolynomial_pos_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℝ}
-- given
  (hz : 0 < z) :
-- imply
  0 < (leeYangPolynomial G beta).eval z := by
-- proof
  apply StatMech.FrontierA.eval_leeYangPolynomial_pos beta hz

/--
[eval_leeYangComplexPolynomial_ofReal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPositiveAxis.lean)
-/
@[path]
private lemma eval_leeYangComplexPolynomial_ofReal_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℝ}
-- given
  (hz : 0 < z) :
-- imply
  (leeYangComplexPolynomial G beta).eval (z : ℂ) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.eval_leeYangComplexPolynomial_ofReal_ne_zero beta hz

/--
[leeYangComplexPolynomial_not_isRoot_ofReal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPositiveAxis.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_not_isRoot_ofReal_pos_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℝ}
-- given
  (hz : 0 < z) :
-- imply
  ¬(leeYangComplexPolynomial G beta).IsRoot (z : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_not_isRoot_ofReal_pos beta hz


-- created on 2026-10-23
