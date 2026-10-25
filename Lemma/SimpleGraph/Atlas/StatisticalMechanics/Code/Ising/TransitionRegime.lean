import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.TransitionRegime
open Real StatMech StatMech.Ising


/--
[abstract_ising_transition_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean)
-/
@[path]
private lemma abstract_ising_transition_regime_eq
  {mStar : ℝ → ℝ}
  {pc : ℝ}
-- given
  (hmag_nonneg_pos : ∀ β, 0 < β → 0 ≤ mStar β)
  (htransition : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta 2 pc < β))
  (hpc0 : 0 < pc)
  (hpc1 : pc < 1) :
-- imply
  0 < pToBeta 2 pc ∧ (∀ β, 0 < β → β < pToBeta 2 pc → mStar β = 0) ∧ (∀ β, pToBeta 2 pc < β → 0 < mStar β) := by
-- proof
  apply StatMech.Ising.abstract_ising_transition_regime mStar pc hmag_nonneg_pos htransition hpc0 hpc1

/--
[betaC_eq_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean)
-/
@[path]
private lemma betaC_eq_regime_eq
  {mStar : ℝ → ℝ}
  {pc : ℝ}
-- given
  (hmag_nonneg_pos : ∀ β, 0 < β → 0 ≤ mStar β)
  (htransition : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta 2 pc < β))
  (hpos : 0 < pToBeta 2 pc) :
-- imply
  IsingFK.betaC mStar = pToBeta 2 pc := by
-- proof
  apply StatMech.Ising.betaC_eq_regime mStar pc hmag_nonneg_pos htransition hpos

/--
[magnetization_nonneg_of_percoId](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean)
-/
@[path]
private lemma magnetization_nonneg_of_percoId_eq
  {d : ℕ}
-- given
  (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)) :
-- imply
  ∀ β, 0 < β → 0 ≤ magnetization d β := by
-- proof
  apply StatMech.Ising.magnetization_nonneg_of_percoId d hmagPercoId

/--
[ising_transition_of_fkPc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean)
-/
@[path]
private lemma ising_transition_of_fkPc_lt_one_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.Ising.ising_transition_of_fkPc_lt_one d hd hmagPercoId hFKsub hpc1

/--
[isingBetaC_eq_of_fkPc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean)
-/
@[path]
private lemma isingBetaC_eq_of_fkPc_lt_one_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.Ising.isingBetaC_eq_of_fkPc_lt_one d hd hmagPercoId hFKsub hpc1

/--
[isingBetaC_pos_of_fkPc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionRegime.lean)
-/
@[path]
private lemma isingBetaC_pos_of_fkPc_lt_one_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.Ising.isingBetaC_pos_of_fkPc_lt_one d hd hmagPercoId hFKsub hpc1


-- created on 2026-10-23
