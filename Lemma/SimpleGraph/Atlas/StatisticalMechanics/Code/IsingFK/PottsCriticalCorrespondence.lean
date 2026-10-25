import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence.Part2
open Real Set StatMech StatMech.FK StatMech.IsingFK


/--
[fkgq_fkTheta_eq_zero_of_lt_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean)
-/
@[path]
private lemma fkgq_fkTheta_eq_zero_of_lt_pc_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hpc : p < fkPc d q) :
-- imply
  fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
-- proof
  apply StatMech.FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq hpc

/--
[betaC_eq_of_strict_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean)
-/
@[path]
private lemma betaC_eq_of_strict_transition_eq
  {mStar : ℝ → ℝ}
  {t : ℝ}
-- given
  (ht : 0 < t)
  (hbelow : ∀ beta, 0 < beta → beta < t → mStar beta = 0)
  (habove : ∀ beta, t < beta → 0 < mStar beta) :
-- imply
  betaC mStar = t := by
-- proof
  apply StatMech.IsingFK.betaC_eq_of_strict_transition mStar t ht hbelow habove

/--
[pottsFKMagnetization_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean)
-/
@[path]
private lemma pottsFKMagnetization_nonneg_eq
  {d : ℕ}
  {q : ℝ}
  {beta : ℝ}
-- given
  (hq : 1 < q) :
-- imply
  0 ≤ pottsFKMagnetization d q hq beta := by
-- proof
  apply StatMech.IsingFK.pottsFKMagnetization_nonneg d q hq beta

/--
[pottsFKMagnetization_eq_zero_of_lt_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean)
-/
@[path]
private lemma pottsFKMagnetization_eq_zero_of_lt_critical_eq
  {d : ℕ}
  {q beta : ℝ}
-- given
  (hq : 1 < q)
  (hpc1 : FK.fkPc d q < 1)
  (hbeta : 0 < beta)
  (hbelow : beta < pToBeta q (FK.fkPc d q)) :
-- imply
  pottsFKMagnetization d q hq beta = 0 := by
-- proof
  apply StatMech.IsingFK.pottsFKMagnetization_eq_zero_of_lt_critical hq hpc1 hbeta hbelow

/--
[pottsFKMagnetization_pos_of_critical_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean)
-/
@[path]
private lemma pottsFKMagnetization_pos_of_critical_lt_eq
  {d : ℕ}
  {q beta : ℝ}
-- given
  (hq : 1 < q)
  (hpc0 : 0 ≤ FK.fkPc d q)
  (hpc1 : FK.fkPc d q < 1)
  (habove : pToBeta q (FK.fkPc d q) < beta) :
-- imply
  0 < pottsFKMagnetization d q hq beta := by
-- proof
  apply StatMech.IsingFK.pottsFKMagnetization_pos_of_critical_lt hq hpc0 hpc1 habove

/--
[pottsFK_betaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean)
-/
@[path]
private lemma pottsFK_betaC_eq_eq
  {d : ℕ}
  {q : ℝ}
-- given
  (hd : 2 ≤ d)
  (hq : 1 < q) :
-- imply
  betaC (pottsFKMagnetization d q hq) = -((q - 1) / q) * Real.log (1 - FK.fkPc d q) := by
-- proof
  apply StatMech.IsingFK.pottsFK_betaC_eq d hd hq


-- created on 2026-10-23
