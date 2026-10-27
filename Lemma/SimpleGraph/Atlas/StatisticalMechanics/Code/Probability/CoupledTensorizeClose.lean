import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.CoupledTensorizeClose
open Finset Real Set StatMech StatMech.Probability


/--
[ctc_sum_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_sum_fin1_eq
  {g : ConfigSpace (Fin 1) → ℝ} :
-- imply
  ∑ ω : ConfigSpace (Fin 1), g ω = g (fun _ => false) + g (fun _ => true) := by
-- proof
  apply StatMech.Probability.ctc_sum_fin1 g

/--
[ctc_weight_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_weight_false_eq
  {p : ℝ} :
-- imply
  OSSS.weight (OSSS.bernoulliWeight p) (fun _ : Fin 1 => false) = 1 - p := by
-- proof
  apply StatMech.Probability.ctc_weight_false p

/--
[ctc_weight_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_weight_true_eq
  {p : ℝ} :
-- imply
  OSSS.weight (OSSS.bernoulliWeight p) (fun _ : Fin 1 => true) = p := by
-- proof
  apply StatMech.Probability.ctc_weight_true p

/--
[ctc_expect_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_expect_fin1_eq
  {p : ℝ}
  {g : ConfigSpace (Fin 1) → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) g = (1 - p) * g (fun _ => false) + p * g (fun _ => true) := by
-- proof
  apply StatMech.Probability.ctc_expect_fin1 p g

/--
[ctc_infl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_infl_eq
  {p : ℝ} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) 0 = 1 := by
-- proof
  apply StatMech.Probability.ctc_infl p

/--
[ctc_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_totalInfl_eq
  {p : ℝ} :
-- imply
  totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) = 1 := by
-- proof
  apply StatMech.Probability.ctc_totalInfl p

/--
[ctc_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_maxInfl_eq
  {p : ℝ} :
-- imply
  maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) = 1 := by
-- proof
  apply StatMech.Probability.ctc_maxInfl p

/--
[ctc_coeff_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_coeff_single_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) {0} = ptn_sigma p := by
-- proof
  apply StatMech.Probability.ctc_coeff_single p hp0 hp1

/--
[ctc_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_mean_eq
  {p : ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) = p := by
-- proof
  apply StatMech.Probability.ctc_mean p

/--
[ctc_L1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_L1_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S ∈ univ.filter (fun S : Finset (Fin 1) => S.card = 1), (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) S) ^ 2) = (ptn_sigma p) ^ 2 := by
-- proof
  apply StatMech.Probability.ctc_L1 p hp0 hp1

/--
[ctc_ge2_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_ge2_empty_eq
  {k : ℕ} :
-- imply
  (univ.filter (fun S : Finset (Fin 1) => 2 ≤ S.card ∧ S.card ≤ k)) = ∅ := by
-- proof
  apply StatMech.Probability.ctc_ge2_empty k

/--
[ctc_varPowerCore_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_varPowerCore_false_eq
  {q : ℝ}
-- given
  (hq : (3:ℝ)/4 < q) :
-- imply
  ¬ vgc_VarPowerCore q := by
-- proof
  apply StatMech.Probability.ctc_varPowerCore_false hq

/--
[ctc_levelGe2_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_levelGe2_false_eq
  {q : ℝ}
-- given
  (hq : (3:ℝ)/4 < q) :
-- imply
  ¬ bkt2_levelGe2MasterResidue q := by
-- proof
  apply StatMech.Probability.ctc_levelGe2_false hq

/--
[ctc_remainingGoal_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_remainingGoal_false_eq
  {q : ℝ}
-- given
  (hq : (3:ℝ)/4 < q) :
-- imply
  ¬ bkt2_RemainingGoal q := by
-- proof
  apply StatMech.Probability.ctc_remainingGoal_false hq

/--
[ctc_varGapCore_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_varGapCore_false_eq
  {q : ℝ}
-- given
  (hq : (3:ℝ)/4 < q) :
-- imply
  ¬ bkt2p_VarGapCore q := by
-- proof
  apply StatMech.Probability.ctc_varGapCore_false hq

/--
[ctc_varScalarCore_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_varScalarCore_false_eq
  {q : ℝ}
-- given
  (hq : (3:ℝ)/4 < q) :
-- imply
  ¬ mil_VarScalarCore q := by
-- proof
  apply StatMech.Probability.ctc_varScalarCore_false hq

/--
[ctc_lowDegree_k0_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_lowDegree_k0_holds_eq
  {p : ℝ}
  {u : ℝ} :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => 1 ≤ S.card ∧ S.card ≤ 0), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) S) ^ 2 ≤ (4 * (ptn_sigma p) ^ 2) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0)) ^ (u / (2 - u)) - (1 - u) ^ (0:ℕ)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) := by
-- proof
  apply StatMech.Probability.ctc_lowDegree_k0_holds p

/--
[ctc_variance_family_all_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeClose.lean)
-/
@[path]
private lemma ctc_variance_family_all_false_eq
  {q : ℝ}
-- given
  (hq : (3:ℝ)/4 < q) :
-- imply
  ¬ vgc_VarPowerCore q ∧ ¬ bkt2p_VarGapCore q ∧ ¬ mil_VarScalarCore q ∧ ¬ bkt2_levelGe2MasterResidue q ∧ ¬ bkt2_RemainingGoal q := by
-- proof
  apply StatMech.Probability.ctc_variance_family_all_false hq


-- created on 2026-10-23
