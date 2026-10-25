import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
open Filter Topology StatMech.FK StatMech StatMech.Walls


/--
[fkc_T_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_T_mul_le_eq
  {d : ℕ}
  {m n : ℕ} :
-- imply
  fkc_T m n * (2 * m + 1) ≤ 2 * n + 1 := by
-- proof
  apply StatMech.Walls.fkc_T_mul_le m n

/--
[fkc_lt_T_succ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_lt_T_succ_mul_eq
  {d : ℕ}
  {m n : ℕ} :
-- imply
  2 * n + 1 < (fkc_T m n + 1) * (2 * m + 1) := by
-- proof
  apply StatMech.Walls.fkc_lt_T_succ_mul m n

/--
[fkc_denom_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_denom_tendsto_atTop_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
-- proof
  apply StatMech.Walls.fkc_denom_tendsto_atTop

/--
[fkc_packing_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_packing_ratio_tendsto_eq
  {d : ℕ}
  {m : ℕ} :
-- imply
  Tendsto (fun n => ((fkc_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) atTop (𝓝 1) := by
-- proof
  apply StatMech.Walls.fkc_packing_ratio_tendsto m

/--
[fkc_oddEven_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_oddEven_ratio_tendsto_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.Walls.fkc_oddEven_ratio_tendsto

/--
[fkc_bulkFraction_arith_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_bulkFraction_arith_tendsto_eq
  {d : ℕ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n : ℕ => ((fkc_T m n) ^ d : ℝ) * ((d : ℝ) * (2 * m) * (2 * (m : ℝ) + 1) ^ (d - 1)) / ((d : ℝ) * (2 * n) * (2 * (n : ℝ) + 1) ^ (d - 1))) atTop (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
-- proof
  apply StatMech.Walls.fkc_bulkFraction_arith_tendsto hd m hm

/--
[fkc_bulkFraction_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbulkfraction.lean)
-/
@[path]
private lemma fkc_bulkFraction_tendsto_eq
  {d : ℕ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n => ((fkc_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
-- proof
  apply StatMech.Walls.fkc_bulkFraction_tendsto hd m hm


-- created on 2026-10-23
