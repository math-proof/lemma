import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationCorrespondence
open MeasureTheory Filter Topology StatMech StatMech.Ising


/--
[mfc_boxBoundaryConnProfile_succ_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_boxBoundaryConnProfile_succ_tendsto_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) (n + 1)) atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) := by
-- proof
  apply StatMech.Ising.mfc_boxBoundaryConnProfile_succ_tendsto hp hp1

/--
[mfc_fvMagnetization_eq_profile_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_fvMagnetization_eq_profile_succ_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {p : ℝ}
  {n : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : (0 : ℝ) < 2)
  (hd : 1 ≤ d)
  (_hn : 1 ≤ n)
  (hisingBox : fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) p (boxOrigin d (n + 1))) :
-- imply
  fvMagnetization d β n = boxBoundaryConnProfile d hp hp1 hq (n + 1) := by
-- proof
  apply StatMech.Ising.mfc_fvMagnetization_eq_profile_succ d β hp hp1 hq hd _hn hisingBox

/--
[mfc_magPercoId](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_magPercoId_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1))) :
-- imply
  ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.Ising.mfc_magPercoId d hd hisingBox

/--
[mfc_htransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_htransition_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) := by
-- proof
  apply StatMech.Ising.mfc_htransition d hd hisingBox hFKsub hpc1

/--
[mfc_ising_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_ising_transition_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.Ising.mfc_ising_transition d hd hmag_nonneg hisingBox hFKsub hpc0 hpc1

/--
[mfc_isingBetaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_isingBetaC_eq_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.Ising.mfc_isingBetaC_eq d hd hmag_nonneg hisingBox hFKsub hpc0 hpc1

/--
[mfc_isingBetaC_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationCorrespondence.lean)
-/
@[path]
private lemma mfc_isingBetaC_pos_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.Ising.mfc_isingBetaC_pos d hd hmag_nonneg hisingBox hFKsub hpc0 hpc1


-- created on 2026-10-23
