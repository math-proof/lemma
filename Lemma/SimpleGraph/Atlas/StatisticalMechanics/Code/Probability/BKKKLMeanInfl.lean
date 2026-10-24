import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.BKKKLMeanInfl
open Finset Real Set StatMech StatMech.Probability


/--
[mil_mean_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_mean_le_one_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 := by
-- proof
  apply StatMech.Probability.mil_mean_le_one hp0 hp1 φ

/--
[mil_mean_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_mean_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mil_mean_nonneg hp0 hp1 φ

/--
[mil_indicator_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_indicator_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {ω : ConfigSpace ι} :
-- imply
  ((fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2 = (fun ω => if φ ω then (1 : ℝ) else 0) ω := by
-- proof
  apply StatMech.Probability.mil_indicator_sq φ ω

/--
[mil_meanSq_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_meanSq_eq_mean_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ((fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2) = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mil_meanSq_eq_mean φ

/--
[mil_var_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_var_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool} :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) - (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
-- proof
  apply StatMech.Probability.mil_var_eq φ

/--
[mil_fourierMass_le_degreeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_fourierMass_le_degreeWeight_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool}
  {p : ℝ} :
-- imply
  ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ ∑ S : Finset ι, (S.card : ℝ) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.mil_fourierMass_le_degreeWeight φ

/--
[mil_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_poincare_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mil_poincare hp0 hp1 φ

/--
[mil_level1_le_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_level1_le_var_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.mil_level1_le_var hp0 hp1 φ

/--
[mil_levelGe2_le_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_levelGe2_le_var_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
  {k : ℕ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * (k : ℝ) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
-- proof
  apply StatMech.Probability.mil_levelGe2_le_var hp0 hp1 φ hu0 hu1 k

/--
[mil_constTrue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_constTrue_eq_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace ι => (1 : ℝ)) := by
-- proof
  apply StatMech.Probability.mil_constTrue_eq

/--
[mil_constTrue_totalInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_constTrue_totalInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ} :
-- imply
  totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) = 0 := by
-- proof
  apply StatMech.Probability.mil_constTrue_totalInfl

/--
[mil_constTrue_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_constTrue_coeff_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {S : Finset ι}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  ptn_coeff p (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) S = if S = ∅ then 1 else 0 := by
-- proof
  apply StatMech.Probability.mil_constTrue_coeff hp0 hp1 S

/--
[mil_constTrue_qnorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_constTrue_qnorm_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {q : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq : 0 < q) :
-- imply
  (ptn_qnorm p q (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)) ^ 2 = 1 := by
-- proof
  apply StatMech.Probability.mil_constTrue_qnorm hp0 hp1 hq

/--
[bkt2f_meanInflResidue_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma bkt2f_meanInflResidue_refutable_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
-- given
  (hq : 1 / 2 < q) :
-- imply
  ¬ bkt2f_meanInflResidue q := by
-- proof
  apply StatMech.Probability.bkt2f_meanInflResidue_refutable hq

/--
[mil_levelGe2_of_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_levelGe2_of_var_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mil_VarScalarCore q} :
-- imply
  bkt2_levelGe2MasterResidue q := by
-- proof
  apply StatMech.Probability.mil_levelGe2_of_var H

/--
[mil_master_of_varScalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_master_of_varScalar_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mil_VarScalarCore q} :
-- imply
  pro_PBiasedMaster q := by
-- proof
  apply StatMech.Probability.mil_master_of_varScalar H

/--
[mil_rhoOptimise_of_varScalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_rhoOptimise_of_varScalar_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : mil_VarScalarCore q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.mil_rhoOptimise_of_varScalar H

/--
[mil_varScalarCore_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLMeanInfl.lean)
-/
@[path]
private lemma mil_varScalarCore_c0_eq
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
  (hu1 : u < 1)
  (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ 4 * ((k : ℝ) + 1) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))) ≤ (4 * (ptn_sigma p) ^ 2) * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) - (1 - u) ^ k) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.mil_varScalarCore_c0 hp0 hp1 hu0 hu1 hδ0


-- created on 2026-10-23
