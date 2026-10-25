import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
open Real Set StatMech StatMech.Probability


/--
[pbt_g_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_g_at_one_eq
  {p q : ℝ} :
-- imply
  pbt_g p q 1 = 1 := by
-- proof
  apply StatMech.Probability.pbt_g_at_one p q

/--
[pbt_core_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_core_at_one_eq
  {p q : ℝ} :
-- imply
  pbt_g p q 1 ≤ ((1 - p) + p * (1:ℝ) ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pbt_core_at_one p q

/--
[pbt_OneVarCore_q_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_OneVarCore_q_one_eq
  {p : ℝ} :
-- imply
  pbt_OneVarCore p 1 := by
-- proof
  apply StatMech.Probability.pbt_OneVarCore_q_one p

/--
[pbt_coeff_slack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_coeff_slack_eq
  {p q : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  0 ≤ p * (1 - p) - (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 := by
-- proof
  apply StatMech.Probability.pbt_coeff_slack hp0 hp1 hq1 hq2

/--
[pbt_lhs_abs_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_lhs_abs_mono_eq
  {p q : ℝ}
  {u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pbt_lhs p q u v ≤ pbt_lhs p q := by
-- proof
  apply StatMech.Probability.pbt_lhs_abs_mono hp0 hp1 hq1 hq2 u v

/--
[pbt_value_pos_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_value_pos_of_core_eq
  {p q : ℝ}
  {Hcore : pbt_OneVarCore p q}
  {u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq0 : 0 < q)
  (hu : 0 < u)
  (hv : 0 ≤ v) :
-- imply
  pbt_lhs p q u v ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pbt_value_pos_of_core hp0 hp1 hq0 Hcore hu hv

/--
[pbt_lhs_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_lhs_reflect_eq
  {p q u v : ℝ} :
-- imply
  pbt_lhs p q u v = pbt_lhs (1 - p) q v u := by
-- proof
  apply StatMech.Probability.pbt_lhs_reflect p q u v

/--
[pbt_value_nonneg_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_value_nonneg_of_core_eq
  {p q : ℝ}
  {Hcore : pbt_OneVarCore p q}
  {Hcore' : pbt_OneVarCore (1 - p) q}
  {u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq0 : 0 < q)
  (hu : 0 ≤ u)
  (hv : 0 ≤ v) :
-- imply
  pbt_lhs p q u v ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pbt_value_nonneg_of_core hp0 hp1 hq0 Hcore Hcore' hu hv

/--
[pbt_two_point_value_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_two_point_value_of_core_eq
  {p q : ℝ}
  {Hcore : pbt_OneVarCore p q}
  {Hcore' : pbt_OneVarCore (1 - p) q}
  {u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pbt_two_point_value_of_core hp0 hp1 hq1 hq2 Hcore Hcore' u v

/--
[pbt_core_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_core_half_eq
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pbt_OneVarCore (1 / 2) q := by
-- proof
  apply StatMech.Probability.pbt_core_half hq1 hq2

/--
[pbt_jensen_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_jensen_mean_eq
  {p q : ℝ}
  {u v : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq1 : 1 ≤ q)
  (hu : 0 ≤ u)
  (hv : 0 ≤ v) :
-- imply
  ((1 - p) * u + p * v) ^ 2 ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pbt_jensen_mean hp0 hp1 hq1 hu hv

/--
[pbt_residue_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_residue_satisfiable_eq :
-- imply
  (∀ p, pbt_OneVarCore p 1) ∧ (∀ q, 1 ≤ q → q ≤ 2 → pbt_OneVarCore (1 / 2) q) := by
-- proof
  apply StatMech.Probability.pbt_residue_satisfiable

/--
[pbt_residue_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_residue_noncirc_eq
  {p q : ℝ}
  {H : pbt_OneVarCore p q}
  {z : ℝ}
-- given
  (hz : 0 ≤ z) :
-- imply
  ((1 - p) + p * z) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2 ≤ ((1 - p) + p * z ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pbt_residue_noncirc H z hz

/--
[pbt_tensorisation_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean)
-/
@[path]
private lemma pbt_tensorisation_reduction_eq :
-- imply
  pbt_TensorisationTarget := by
-- proof
  apply StatMech.Probability.pbt_tensorisation_reduction


-- created on 2026-10-23
