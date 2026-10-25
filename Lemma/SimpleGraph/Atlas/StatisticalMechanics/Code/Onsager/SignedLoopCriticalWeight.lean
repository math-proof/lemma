import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
open StatMech StatMech.Onsager


/--
[ons_betaC_eq_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma ons_betaC_eq_selfDualPoint_eq :
-- imply
  ons_betaC = StatMech.Ising.selfDualPoint := by
-- proof
  apply StatMech.Onsager.ons_betaC_eq_selfDualPoint

/--
[ons_signedLoopCriticalWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma ons_signedLoopCriticalWeight_pos_eq :
-- imply
  0 < ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.ons_signedLoopCriticalWeight_pos

/--
[ons_signedLoopCriticalWeight_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma ons_signedLoopCriticalWeight_lt_one_eq :
-- imply
  ons_signedLoopCriticalWeight < 1 := by
-- proof
  apply StatMech.Onsager.ons_signedLoopCriticalWeight_lt_one

/--
[exp_neg_two_ons_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma exp_neg_two_ons_betaC_eq :
-- imply
  Real.exp (-2 * ons_betaC) = ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.exp_neg_two_ons_betaC

/--
[tanh_ons_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma tanh_ons_betaC_eq :
-- imply
  Real.tanh ons_betaC = ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.tanh_ons_betaC

/--
[tanh_lt_signedLoopCriticalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma tanh_lt_signedLoopCriticalWeight_eq
  {beta : ℝ}
-- given
  (hbeta : beta < ons_betaC) :
-- imply
  Real.tanh beta < ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.tanh_lt_signedLoopCriticalWeight hbeta

/--
[tanh_le_signedLoopCriticalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma tanh_le_signedLoopCriticalWeight_eq
  {beta : ℝ}
-- given
  (hbeta : beta ≤ ons_betaC) :
-- imply
  Real.tanh beta ≤ ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.tanh_le_signedLoopCriticalWeight hbeta

/--
[exp_neg_two_lt_signedLoopCriticalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma exp_neg_two_lt_signedLoopCriticalWeight_eq
  {beta : ℝ}
-- given
  (hbeta : ons_betaC < beta) :
-- imply
  Real.exp (-2 * beta) < ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.exp_neg_two_lt_signedLoopCriticalWeight hbeta

/--
[exp_neg_two_le_signedLoopCriticalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma exp_neg_two_le_signedLoopCriticalWeight_eq
  {beta : ℝ}
-- given
  (hbeta : ons_betaC ≤ beta) :
-- imply
  Real.exp (-2 * beta) ≤ ons_signedLoopCriticalWeight := by
-- proof
  apply StatMech.Onsager.exp_neg_two_le_signedLoopCriticalWeight hbeta

/--
[sqrt_two_add_one_mul_signedLoopCriticalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma sqrt_two_add_one_mul_signedLoopCriticalWeight_eq :
-- imply
  (Real.sqrt 2 + 1) * ons_signedLoopCriticalWeight = 1 := by
-- proof
  apply StatMech.Onsager.sqrt_two_add_one_mul_signedLoopCriticalWeight

/--
[signedLoopCriticalWeight_eq_inv_sqrt_two_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean)
-/
@[path]
private lemma signedLoopCriticalWeight_eq_inv_sqrt_two_add_one_eq :
-- imply
  ons_signedLoopCriticalWeight = (Real.sqrt 2 + 1)⁻¹ := by
-- proof
  apply StatMech.Onsager.signedLoopCriticalWeight_eq_inv_sqrt_two_add_one


-- created on 2026-10-23
