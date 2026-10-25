import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
open Finset Polynomial StatMech StatMech.FrontierB


/--
[sum_spin_eq_card_sub_two_mul_minusSpinCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma sum_spin_eq_card_sub_two_mul_minusSpinCount_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  (∑ x, spin s x) = (Fintype.card V : ℝ) - 2 * minusSpinCount s := by
-- proof
  apply StatMech.FrontierB.sum_spin_eq_card_sub_two_mul_minusSpinCount s

/--
[eval_leeYangPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma eval_leeYangPolynomial_eq
  [Fintype V]
  [DecidableEq V]
  {β z : ℝ} :
-- imply
  (leeYangPolynomial G β).eval z = ∑ s : ConfigSpace V, zeroFieldInteractionWeight G β s * z ^ minusSpinCount s := by
-- proof
  apply StatMech.FrontierB.eval_leeYangPolynomial β z

/--
[interactionWeight_mul_fugacity_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma interactionWeight_mul_fugacity_pow_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  zeroFieldInteractionWeight G β s * Real.exp (-2 * β * h) ^ minusSpinCount s = Real.exp (-β * h * Fintype.card V) * isingWeight G β h s := by
-- proof
  apply StatMech.FrontierB.interactionWeight_mul_fugacity_pow β h s

/--
[eval_leeYangPolynomial_at_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma eval_leeYangPolynomial_at_fugacity_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (β h : ℝ) :
-- imply
  (leeYangPolynomial G β).eval (Real.exp (-2 * β * h)) = Real.exp (-β * h * Fintype.card V) * isingZ G β h := by
-- proof
  apply StatMech.FrontierB.eval_leeYangPolynomial_at_fugacity β h

/--
[eval_leeYangComplexPolynomial_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma eval_leeYangComplexPolynomial_ofReal_eq
  [Fintype V]
  [DecidableEq V]
  {β z : ℝ} :
-- imply
  (leeYangComplexPolynomial G β).eval (z : ℂ) = Complex.ofReal ((leeYangPolynomial G β).eval z) := by
-- proof
  apply StatMech.FrontierB.eval_leeYangComplexPolynomial_ofReal β z

/--
[leeYangPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma leeYangPolynomial_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  leeYangPolynomial G β ≠ 0 := by
-- proof
  apply StatMech.FrontierB.leeYangPolynomial_ne_zero β

/--
[leeYangComplexPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  leeYangComplexPolynomial G β ≠ 0 := by
-- proof
  apply StatMech.FrontierB.leeYangComplexPolynomial_ne_zero β


-- created on 2026-10-23
