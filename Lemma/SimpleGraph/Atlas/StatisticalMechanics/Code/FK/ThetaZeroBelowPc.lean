import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.ThetaZeroBelowPc
open MeasureTheory Filter Topology StatMech StatMech.FK


/--
[tzp_fkTheta_iv_monotone_boxBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ThetaZeroBelowPc.lean)
-/
@[path]
private lemma tzp_fkTheta_iv_monotone_boxBdry_eq
  {d : ℕ}
  {n : ℕ}
  {p₁ p₂ : ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂) :
-- imply
  (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.tzp_fkTheta_iv_monotone_boxBdry n hp₁ hp₁' hp₂ hp₂' hle

/--
[tzp_fkTheta_monotone_in_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ThetaZeroBelowPc.lean)
-/
@[path]
private lemma tzp_fkTheta_monotone_in_p_eq
  {d : ℕ}
  {p₁ p₂ : ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp₁' : p₁ < 1)
  (hp₂ : 0 < p₂)
  (hp₂' : p₂ < 1)
  (hle : p₁ ≤ p₂) :
-- imply
  fkTheta d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2) (q := 2) ≤ fkTheta d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.FK.tzp_fkTheta_monotone_in_p hp₁ hp₁' hp₂ hp₂' hle

/--
[tzp_fkTheta_eq_zero_of_lt_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ThetaZeroBelowPc.lean)
-/
@[path]
private lemma tzp_fkTheta_eq_zero_of_lt_pc_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hpc : p < FK.fkPc d 2) :
-- imply
  FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
-- proof
  apply StatMech.FK.tzp_fkTheta_eq_zero_of_lt_pc hp hp1 hpc

/--
[tzp_fkTheta_eq_zero_of_le_pc_of_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ThetaZeroBelowPc.lean)
-/
@[path]
private lemma tzp_fkTheta_eq_zero_of_le_pc_of_pc_eq
  {d : ℕ}
-- given
  (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1), FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
-- imply
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
-- proof
  apply StatMech.FK.tzp_fkTheta_eq_zero_of_le_pc_of_pc hθpc


-- created on 2026-10-23
