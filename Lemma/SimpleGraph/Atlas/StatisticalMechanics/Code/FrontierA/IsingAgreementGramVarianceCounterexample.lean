import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingAgreementGramVarianceCounterexample
open StatMech StatMech.FrontierA


/--
[gramVarianceCounterKernel_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterKernel_pos_eq
  {i j : Fin 3} :
-- imply
  0 < gramVarianceCounterKernel i j := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterKernel_pos i j

/--
[gramVarianceCounterKernel_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterKernel_symm_eq
  {i j : Fin 3} :
-- imply
  gramVarianceCounterKernel i j = gramVarianceCounterKernel j i := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterKernel_symm i j

/--
[gramVarianceCounterKernel_quadratic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterKernel_quadratic_nonneg_eq
-- given
  (f : Fin 3 -> Real) :
-- imply
  0 <= ∑ i, ∑ j, f i * gramVarianceCounterKernel i j * f j := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterKernel_quadratic_nonneg f

/--
[gramVarianceCounterMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterMass_zero_eq :
-- imply
  gramVarianceCounterMass 0 = 1 := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterMass_zero

/--
[gramVarianceCounterMass_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterMass_one_eq :
-- imply
  gramVarianceCounterMass 1 = 8 := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterMass_one

/--
[gramVarianceCounterMass_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterMass_two_eq :
-- imply
  gramVarianceCounterMass 2 = 2 := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterMass_two

/--
[gramVarianceCounterMass_compl_ratio_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterMass_compl_ratio_mono_eq
  {i j : Fin 3}
-- given
  (hij : i <= j) :
-- imply
  gramVarianceCounterMass i * gramVarianceCounterMass (gramVarianceCounterReflect j) <= gramVarianceCounterMass j * gramVarianceCounterMass (gramVarianceCounterReflect i) := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterMass_compl_ratio_mono hij

/--
[gramVarianceCounterPlusVariance_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterPlusVariance_eq_eq :
-- imply
  finiteWeightedVariance gramVarianceCounterPlusWeight gramVarianceCounterValue = 192 / 175 := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterPlusVariance_eq

/--
[gramVarianceCounterMinusVariance_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterMinusVariance_eq_eq :
-- imply
  finiteWeightedVariance gramVarianceCounterMinusWeight gramVarianceCounterValue = 4416 / 4225 := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterMinusVariance_eq

/--
[gramVarianceCounterMinusVariance_lt_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean)
-/
@[path]
private lemma gramVarianceCounterMinusVariance_lt_plus_eq :
-- imply
  finiteWeightedVariance gramVarianceCounterMinusWeight gramVarianceCounterValue < finiteWeightedVariance gramVarianceCounterPlusWeight gramVarianceCounterValue := by
-- proof
  apply StatMech.FrontierA.gramVarianceCounterMinusVariance_lt_plus


-- created on 2026-10-23
