import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperPeierls
open MeasureTheory Filter Topology StatMech StatMech.IsingFK


/--
[pup_fvMagnetization_eq_fvMagOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma pup_fvMagnetization_eq_fvMagOrigin_eq
  {n : ℕ}
  {β : ℝ} :
-- imply
  fvMagnetization 2 β n = fvMagOrigin (plusField 2) n (bondFinsetTouch 2 n) β 0 := by
-- proof
  apply StatMech.IsingFK.pup_fvMagnetization_eq_fvMagOrigin n β

/--
[pup_fkPc_le_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma pup_fkPc_le_of_fkTheta_pos_eq
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hθ : 0 < fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)) :
-- imply
  fkPc 2 2 ≤ p := by
-- proof
  apply StatMech.IsingFK.pup_fkPc_le_of_fkTheta_pos hp hp1 hθ

/--
[pup_exists_uniform_fvMagnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma pup_exists_uniform_fvMagnetization_eq :
-- imply
  ∃ β > 0, ∃ c > 0, ∀ n, c ≤ fvMagnetization 2 β n := by
-- proof
  apply StatMech.IsingFK.pup_exists_uniform_fvMagnetization

/--
[pup_exists_positive_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma pup_exists_positive_magnetization_eq :
-- imply
  ∃ β > 0, 0 < magnetization 2 β := by
-- proof
  apply StatMech.IsingFK.pup_exists_positive_magnetization

/--
[fkPc_two_two_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma fkPc_two_two_lt_one_eq :
-- imply
  fkPc 2 2 < 1 := by
-- proof
  apply StatMech.IsingFK.fkPc_two_two_lt_one

/--
[ising_transition_two_at_fkPc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma ising_transition_two_at_fkPc_eq :
-- imply
  0 < pToBeta 2 (fkPc 2 2) ∧ (∀ β, 0 < β → β < pToBeta 2 (fkPc 2 2) → magnetization 2 β = 0) ∧ (∀ β, pToBeta 2 (fkPc 2 2) < β → 0 < magnetization 2 β) := by
-- proof
  apply StatMech.IsingFK.ising_transition_two_at_fkPc

/--
[ising_transition_two_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma ising_transition_two_unconditional_eq :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization 2 β = 0) ∧ (∀ β, βc < β → 0 < magnetization 2 β) := by
-- proof
  apply StatMech.IsingFK.ising_transition_two_unconditional

/--
[isingBetaC_two_eq_fkPc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PcUpperPeierls.lean)
-/
@[path]
private lemma isingBetaC_two_eq_fkPc_eq :
-- imply
  betaC (magnetization 2) = -(1 / 2) * Real.log (1 - fkPc 2 2) := by
-- proof
  apply StatMech.IsingFK.isingBetaC_two_eq_fkPc


-- created on 2026-10-23
