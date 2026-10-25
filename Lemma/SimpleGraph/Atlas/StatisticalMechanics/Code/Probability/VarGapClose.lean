import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.VarGapClose.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[vgc_totalInfl_zero_of_maxInfl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_totalInfl_zero_of_maxInfl_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
-- imply
  totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
-- proof
  apply StatMech.Probability.vgc_totalInfl_zero_of_maxInfl_zero hp0 hp1 φ hδ0

/--
[vgc_var_zero_of_maxInfl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_var_zero_of_maxInfl_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) = 0 := by
-- proof
  apply StatMech.Probability.vgc_var_zero_of_maxInfl_zero hp0 hp1 φ hδ0

/--
[vgc_varGapCore_of_varPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_varGapCore_of_varPower_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : vgc_VarPowerCore q} :
-- imply
  bkt2p_VarGapCore q := by
-- proof
  apply StatMech.Probability.vgc_varGapCore_of_varPower H

/--
[vgc_levelGe2_of_varPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_levelGe2_of_varPower_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : vgc_VarPowerCore q} :
-- imply
  bkt2_levelGe2MasterResidue q := by
-- proof
  apply StatMech.Probability.vgc_levelGe2_of_varPower H

/--
[vgc_remaining_of_varPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_remaining_of_varPower_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : vgc_VarPowerCore q} :
-- imply
  bkt2_RemainingGoal q := by
-- proof
  apply StatMech.Probability.vgc_remaining_of_varPower H

/--
[vgc_master_of_varPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_master_of_varPower_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : vgc_VarPowerCore q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.vgc_master_of_varPower H

/--
[vgc_rhoOptimise_of_varPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_rhoOptimise_of_varPower_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : vgc_VarPowerCore q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.vgc_rhoOptimise_of_varPower H

/--
[vgc_varPowerCore_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_varPowerCore_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (_hu1 : u < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ≤ (u / (4 + 2 * u)) * ((ptn_sigma p) ^ 2 * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))) := by
-- proof
  apply StatMech.Probability.vgc_varPowerCore_c0 hp0 hp1 hu0 _hu1

/--
[vgc_poincare_is_delta0_instance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_poincare_is_delta0_instance_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.vgc_poincare_is_delta0_instance hp0 hp1 φ

/--
[vgc_gap_vanishes_at_p_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean)
-/
@[path]
private lemma vgc_gap_vanishes_at_p_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {u : ℝ}
  {d : ℕ} :
-- imply
  (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
-- proof
  apply StatMech.Probability.vgc_gap_vanishes_at_p_half d


-- created on 2026-10-23
