import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.fc_bulkfraction
open Filter Topology StatMech.FK StatMech StatMech.Walls


/--
[fc_T_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_T_mul_le_eq
  {d : ℕ}
  {m n : ℕ} :
-- imply
  fc_T m n * (2 * m + 1) ≤ 2 * n + 1 := by
-- proof
  apply StatMech.Walls.fc_T_mul_le m n

/--
[fc_lt_T_succ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_lt_T_succ_mul_eq
  {d : ℕ}
  {m n : ℕ} :
-- imply
  2 * n + 1 < (fc_T m n + 1) * (2 * m + 1) := by
-- proof
  apply StatMech.Walls.fc_lt_T_succ_mul m n

/--
[fc_denom_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_denom_tendsto_atTop_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
-- proof
  apply StatMech.Walls.fc_denom_tendsto_atTop

/--
[fc_packing_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_packing_ratio_tendsto_eq
  {d : ℕ}
  {m : ℕ} :
-- imply
  Tendsto (fun n => ((fc_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) atTop (𝓝 1) := by
-- proof
  apply StatMech.Walls.fc_packing_ratio_tendsto m

/--
[fc_oddEven_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_oddEven_ratio_tendsto_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.Walls.fc_oddEven_ratio_tendsto

/--
[fc_bulkFraction_arith_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_bulkFraction_arith_tendsto_eq
  {d : ℕ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n : ℕ => ((fc_T m n) ^ d : ℝ) * ((d : ℝ) * (2 * m) * (2 * (m : ℝ) + 1) ^ (d - 1)) / ((d : ℝ) * (2 * n) * (2 * (n : ℝ) + 1) ^ (d - 1))) atTop (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
-- proof
  apply StatMech.Walls.fc_bulkFraction_arith_tendsto hd m hm

/--
[fc_bulkFraction_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean)
-/
@[path]
private lemma fc_bulkFraction_tendsto_eq
  {d : ℕ}
  {m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : 1 ≤ m) :
-- imply
  Tendsto (fun n => ((fc_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
-- proof
  apply StatMech.Walls.fc_bulkFraction_tendsto hd m hm


-- created on 2026-10-23
