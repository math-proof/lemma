import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoId
open MeasureTheory Filter Topology StatMech StatMech.IsingFK


/--
[boundaryConnProfile_tendsto_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoId.lean)
-/
@[path]
private lemma boundaryConnProfile_tendsto_fkTheta_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Tendsto (fun n => boundaryConnProfile d hp hp1 hq n) atTop (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
-- proof
  apply StatMech.IsingFK.boundaryConnProfile_tendsto_fkTheta hp hp1 hq

/--
[magPercoId_of_fvES](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoId.lean)
-/
@[path]
private lemma magPercoId_of_fvES_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : (0 : ℝ) < 2)
  (hfvES : ∀ n, fvMagnetization d β n = boundaryConnProfile d hp hp1 hq n) :
-- imply
  magnetization d β = fkTheta d hp hp1 hq (q := 2) := by
-- proof
  apply StatMech.IsingFK.magPercoId_of_fvES d β hp hp1 hq hfvES

/--
[magPercoId_final](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoId.lean)
-/
@[path]
private lemma magPercoId_final_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hfvES : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1) (n : ℕ), fvMagnetization d β n = boundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n) :
-- imply
  ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.IsingFK.magPercoId_final d hfvES

/--
[ising_transition_of_fvES_of_fkPc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoId.lean)
-/
@[path]
private lemma ising_transition_of_fvES_of_fkPc_lt_one_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hfvES : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1) (n : ℕ), fvMagnetization d β n = boundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.IsingFK.ising_transition_of_fvES_of_fkPc_lt_one d hd hfvES hFKsub hpc1

/--
[isingBetaC_eq_of_fvES_of_fkPc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoId.lean)
-/
@[path]
private lemma isingBetaC_eq_of_fvES_of_fkPc_lt_one_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hfvES : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1) (n : ℕ), fvMagnetization d β n = boundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
  (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.IsingFK.isingBetaC_eq_of_fvES_of_fkPc_lt_one d hd hfvES hFKsub hpc1


-- created on 2026-10-23
