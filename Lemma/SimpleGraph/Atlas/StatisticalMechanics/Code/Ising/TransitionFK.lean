import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
open Real StatMech StatMech.Ising


/--
[pOfBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma pOfBeta_pos_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  0 < pOfBeta β := by
-- proof
  apply StatMech.Ising.pOfBeta_pos hβ

/--
[pOfBeta_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma pOfBeta_lt_one_eq
  {β : ℝ} :
-- imply
  pOfBeta β < 1 := by
-- proof
  apply StatMech.Ising.pOfBeta_lt_one β

/--
[fkRoute_pOfBeta_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma fkRoute_pOfBeta_mem_Ioo_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  pOfBeta β ∈ Set.Ioo (0 : ℝ) 1 := by
-- proof
  apply StatMech.Ising.fkRoute_pOfBeta_mem_Ioo hβ

/--
[fkRoute_pToBeta_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma fkRoute_pToBeta_pOfBeta_eq
  {β : ℝ} :
-- imply
  pToBeta 2 (pOfBeta β) = β := by
-- proof
  apply StatMech.Ising.fkRoute_pToBeta_pOfBeta β

/--
[fkTheta_pos_of_fkPc_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma fkTheta_pos_of_fkPc_lt_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpc : FK.fkPc d 2 < p) :
-- imply
  0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.Ising.fkTheta_pos_of_fkPc_lt d hp hp1 hpc

/--
[fkPc_lt_pOfBeta_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma fkPc_lt_pOfBeta_iff_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (_hβ : 0 < β)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  FK.fkPc d 2 < pOfBeta β ↔ pToBeta 2 (FK.fkPc d 2) < β := by
-- proof
  apply StatMech.Ising.fkPc_lt_pOfBeta_iff d _hβ hpc1

/--
[fkTheta_pos_iff_fkPc_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma fkTheta_pos_iff_fkPc_lt_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
-- imply
  0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) ↔ FK.fkPc d 2 < p := by
-- proof
  apply StatMech.Ising.fkTheta_pos_iff_fkPc_lt d hp hp1 hFKsub

/--
[htransition_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma htransition_fk_eq
  {d : ℕ}
-- given
  (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), (0 < magnetization d β ↔ 0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) := by
-- proof
  apply StatMech.Ising.htransition_fk d hmagPerco hFKsub hpc1

/--
[htransition_fk_of_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma htransition_fk_of_identity_eq
  {d : ℕ}
-- given
  (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) := by
-- proof
  apply StatMech.Ising.htransition_fk_of_identity d hmagPercoId hFKsub hpc1

/--
[ising_transition_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma ising_transition_fk_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), (0 < magnetization d β ↔ 0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.Ising.ising_transition_fk d hd hmag_nonneg hmagPerco hFKsub hpc1

/--
[isingBetaC_eq_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma isingBetaC_eq_fk_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), (0 < magnetization d β ↔ 0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.Ising.isingBetaC_eq_fk d hd hmag_nonneg hmagPerco hFKsub hpc1

/--
[isingBetaC_pos_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionFK.lean)
-/
@[path]
private lemma isingBetaC_pos_fk_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), (0 < magnetization d β ↔ 0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.Ising.isingBetaC_pos_fk d hd hmag_nonneg hmagPerco hFKsub hpc1


-- created on 2026-10-23
