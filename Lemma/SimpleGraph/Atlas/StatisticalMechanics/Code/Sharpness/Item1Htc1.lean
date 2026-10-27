import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.Item1Htc1
open MeasureTheory Set Filter Topology Real StatMech StatMech.Sharpness


/--
[sh1_tildePc_lt_one_of_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Item1Htc1.lean)
-/
@[path]
private lemma sh1_tildePc_lt_one_of_pc_lt_one_eq
  {d : ℕ}
-- given
  (hd : 0 < d)
  (hpc : pc d < 1) :
-- imply
  (tildePc d : ℝ) < 1 := by
-- proof
  apply StatMech.Sharpness.sh1_tildePc_lt_one_of_pc_lt_one hd hpc

/--
[sh1_betaTildeC_pos_of_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Item1Htc1.lean)
-/
@[path]
private lemma sh1_betaTildeC_pos_of_pc_lt_one_eq
  {d : ℕ}
  {J : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (hpc : pc d < 1) :
-- imply
  0 < betaTildeC d J := by
-- proof
  apply StatMech.Sharpness.sh1_betaTildeC_pos_of_pc_lt_one hJ hd hpc

/--
[sh1_theta_ge_betaForm_of_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Item1Htc1.lean)
-/
@[path]
private lemma sh1_theta_ge_betaForm_of_pc_lt_one_eq
  {d : ℕ}
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (hpc : pc d < 1)
  (hβ : betaTildeC d J < β) :
-- imply
  theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) ≥ (β - betaTildeC d J) / β := by
-- proof
  apply StatMech.Sharpness.sh1_theta_ge_betaForm_of_pc_lt_one hJ hd hpc hβ


-- created on 2026-10-23
