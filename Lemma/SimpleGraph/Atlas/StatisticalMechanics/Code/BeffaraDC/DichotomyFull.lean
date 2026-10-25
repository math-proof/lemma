import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.DichotomyFull
open StatMech StatMech.BeffaraDC


/--
[mem_subcritical_of_lt_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/DichotomyFull.lean)
-/
@[path]
private lemma mem_subcritical_of_lt_selfDualPoint_eq
  {q : ℝ}
  {p : ℝ}
-- given
  (hq : 1 ≤ q)
  (hp0 : 0 < p)
  (hp_sd : p < selfDualPoint q)
  (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
-- imply
  p ∈ fkSubcriticalSet 2 q := by
-- proof
  apply StatMech.BeffaraDC.mem_subcritical_of_lt_selfDualPoint hq hp0 hp_sd hNoPercBelow

/--
[selfDualPoint_subcritical_le_fkPc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/DichotomyFull.lean)
-/
@[path]
private lemma selfDualPoint_subcritical_le_fkPc_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
-- imply
  selfDualPoint q ≤ fkPc 2 q := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_subcritical_le_fkPc hq hNoPercBelow

/--
[fkPc_le_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/DichotomyFull.lean)
-/
@[path]
private lemma fkPc_le_selfDualPoint_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
-- imply
  fkPc 2 q ≤ selfDualPoint q := by
-- proof
  apply StatMech.BeffaraDC.fkPc_le_selfDualPoint hq hPercAbove

/--
[fkPc_eq_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/DichotomyFull.lean)
-/
@[path]
private lemma fkPc_eq_selfDualPoint_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0)
  (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
-- imply
  fkPc 2 q = selfDualPoint q := by
-- proof
  apply StatMech.BeffaraDC.fkPc_eq_selfDualPoint hq hNoPercBelow hPercAbove

/--
[beffaraDC_critical_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/DichotomyFull.lean)
-/
@[path]
private lemma beffaraDC_critical_point_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), r < Real.sqrt q / (1 + Real.sqrt q) → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0)
  (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1), Real.sqrt q / (1 + Real.sqrt q) < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
-- imply
  fkPc 2 q = Real.sqrt q / (1 + Real.sqrt q) := by
-- proof
  apply StatMech.BeffaraDC.beffaraDC_critical_point hq hNoPercBelow hPercAbove


-- created on 2026-10-23
