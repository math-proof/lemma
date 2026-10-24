import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
open Finset Polynomial StatMech StatMech.FrontierA


/--
[minusSpinCount_isingSumConfigEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma minusSpinCount_isingSumConfigEquiv_symm_eq
  [Fintype V]
  [Fintype W]
  {s : ConfigSpace V}
  {t : ConfigSpace W} :
-- imply
  minusSpinCount (isingSumConfigEquiv.symm (s, t)) = minusSpinCount s + minusSpinCount t := by
-- proof
  apply StatMech.FrontierA.minusSpinCount_isingSumConfigEquiv_symm s t

/--
[zeroFieldInteractionWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma zeroFieldInteractionWeight_sum_eq
  [Fintype V]
  [Fintype W]
  {beta : ℝ}
  {s : ConfigSpace V}
  {t : ConfigSpace W} :
-- imply
  zeroFieldInteractionWeight (G ⊕g H) beta (isingSumConfigEquiv.symm (s, t)) = zeroFieldInteractionWeight G beta s * zeroFieldInteractionWeight H beta t := by
-- proof
  apply StatMech.FrontierA.zeroFieldInteractionWeight_sum beta s t

/--
[leeYangPolynomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma leeYangPolynomial_sum_eq
  [Fintype V]
  [Fintype W]
  {beta : ℝ} :
-- imply
  leeYangPolynomial (G ⊕g H) beta = leeYangPolynomial G beta * leeYangPolynomial H beta := by
-- proof
  apply StatMech.FrontierA.leeYangPolynomial_sum beta

/--
[leeYangComplexPolynomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_sum_eq
  [Fintype V]
  [Fintype W]
  {beta : ℝ} :
-- imply
  leeYangComplexPolynomial (G ⊕g H) beta = leeYangComplexPolynomial G beta * leeYangComplexPolynomial H beta := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_sum beta

/--
[zeroFieldInteractionWeight_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma zeroFieldInteractionWeight_bot_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {s : ConfigSpace V} :
-- imply
  zeroFieldInteractionWeight (⊥ : SimpleGraph V) beta s = 1 := by
-- proof
  apply StatMech.FrontierA.zeroFieldInteractionWeight_bot beta s

/--
[sum_X_pow_minusSpinCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma sum_X_pow_minusSpinCount_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  (∑ s : ConfigSpace V, (X : ℝ[X]) ^ minusSpinCount s) = (1 + X) ^ Fintype.card V := by
-- proof
  apply StatMech.FrontierA.sum_X_pow_minusSpinCount

/--
[leeYangPolynomial_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma leeYangPolynomial_bot_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  leeYangPolynomial (⊥ : SimpleGraph V) beta = (1 + X) ^ Fintype.card V := by
-- proof
  apply StatMech.FrontierA.leeYangPolynomial_bot beta

/--
[leeYangComplexPolynomial_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_bot_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ} :
-- imply
  leeYangComplexPolynomial (⊥ : SimpleGraph V) beta = (1 + X) ^ Fintype.card V := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_bot beta

/--
[leeYangComplexPolynomial_bot_root_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_bot_root_eq_neg_one_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hz : (leeYangComplexPolynomial (⊥ : SimpleGraph V) beta).eval z = 0) :
-- imply
  z = -1 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_bot_root_eq_neg_one beta hz

/--
[leeYangComplexPolynomial_bot_root_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangDisjointUnion.lean)
-/
@[path]
private lemma leeYangComplexPolynomial_bot_root_norm_eq
  [Fintype V]
  [DecidableEq V]
  {beta : ℝ}
  {z : ℂ}
-- given
  (hz : (leeYangComplexPolynomial (⊥ : SimpleGraph V) beta).eval z = 0) :
-- imply
  ‖z‖ = 1 := by
-- proof
  apply StatMech.FrontierA.leeYangComplexPolynomial_bot_root_norm beta hz


-- created on 2026-10-23
