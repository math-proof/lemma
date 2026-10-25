import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part5
open StatMech StatMech.Universality


/--
[zd_mem_sawWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_mem_sawWalks_eq
  {d n : ℕ}
  {w : Fin n → ZdStep d} :
-- imply
  w ∈ zdSAWWalks d n ↔ ZdIsSAW w := by
-- proof
  apply StatMech.Universality.zd_mem_sawWalks

/--
[zd_mem_nbWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_mem_nbWalks_eq
  {d n : ℕ}
  {w : Fin n → ZdStep d} :
-- imply
  w ∈ zdNBWalks d n ↔ ZdIsNB w := by
-- proof
  apply StatMech.Universality.zd_mem_nbWalks

/--
[zdStepVec_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zdStepVec_reverse_eq
  {d : ℕ}
  {s : ZdStep d} :
-- imply
  zdStepVec (zdReverse s) = - zdStepVec s := by
-- proof
  apply StatMech.Universality.zdStepVec_reverse s

/--
[zdPos_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zdPos_succ_eq
  {d n : ℕ}
  {w : Fin n → ZdStep d}
  {k : ℕ} :
-- imply
  zdPos w (k + 1) = zdPos w k + zdStepN w k := by
-- proof
  apply StatMech.Universality.zdPos_succ w k

/--
[zd_card_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_card_step_eq
  {d : ℕ} :
-- imply
  Fintype.card (ZdStep d) = 2 * d := by
-- proof
  apply StatMech.Universality.zd_card_step d

/--
[zd_card_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_card_ne_eq
  {d : ℕ}
  {t : ZdStep d} :
-- imply
  (Finset.univ.filter (fun s : ZdStep d => s ≠ t)).card = 2 * d - 1 := by
-- proof
  apply StatMech.Universality.zd_card_ne d t

/--
[zd_sum_stepVec_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_sum_stepVec_pos_eq
  {d : ℕ}
  {i : Fin d} :
-- imply
  ∑ j : Fin d, zdStepVec ((i, true) : ZdStep d) j = 1 := by
-- proof
  apply StatMech.Universality.zd_sum_stepVec_pos i

/--
[zd_totalSum_wOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_totalSum_wOf_eq
  {d n : ℕ}
  {σ : Fin n → Fin d}
  {k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  ∑ j : Fin d, (zdPos (zdWOf σ) k) j = (k : ℤ) := by
-- proof
  apply StatMech.Universality.zd_totalSum_wOf σ k hk

/--
[zd_isSAW_wOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_isSAW_wOf_eq
  {d n : ℕ}
  {σ : Fin n → Fin d} :
-- imply
  ZdIsSAW (zdWOf σ) := by
-- proof
  apply StatMech.Universality.zd_isSAW_wOf σ

/--
[zd_wOf_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_wOf_injective_eq
  {d n : ℕ} :
-- imply
  Function.Injective (zdWOf : (Fin n → Fin d) → _) := by
-- proof
  apply StatMech.Universality.zd_wOf_injective

/--
[zd_pow_le_sawCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_pow_le_sawCount_eq
  {d n : ℕ} :
-- imply
  d ^ n ≤ zdSAWCount d n := by
-- proof
  apply StatMech.Universality.zd_pow_le_sawCount

/--
[zd_isSAW_isNB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_isSAW_isNB_eq
  {d n : ℕ}
  {w : Fin n → ZdStep d}
-- given
  (hw : ZdIsSAW w) :
-- imply
  ZdIsNB w := by
-- proof
  apply StatMech.Universality.zd_isSAW_isNB hw

/--
[zd_sawWalks_subset_nbWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_sawWalks_subset_nbWalks_eq
  {d n : ℕ} :
-- imply
  zdSAWWalks d n ⊆ zdNBWalks d n := by
-- proof
  apply StatMech.Universality.zd_sawWalks_subset_nbWalks

/--
[zd_dropLast_isNB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_dropLast_isNB_eq
  {d n : ℕ}
  {w : Fin (n + 1) → ZdStep d}
-- given
  (hw : ZdIsNB w) :
-- imply
  ZdIsNB (zdDropLast w) := by
-- proof
  apply StatMech.Universality.zd_dropLast_isNB hw

/--
[zd_fiber_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_fiber_card_le_eq
  {d n : ℕ}
  {v : Fin n → ZdStep d}
-- given
  (hn : 1 ≤ n) :
-- imply
  ({w ∈ zdNBWalks d (n + 1) | zdDropLast w = v}).card ≤ 2 * d - 1 := by
-- proof
  apply StatMech.Universality.zd_fiber_card_le hn v

/--
[zd_nbCount_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_nbCount_succ_le_eq
  {d n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  zdNBCount d (n + 1) ≤ (2 * d - 1) * zdNBCount d n := by
-- proof
  apply StatMech.Universality.zd_nbCount_succ_le hn

/--
[zd_nbCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_nbCount_one_eq
  {d : ℕ} :
-- imply
  zdNBCount d 1 = 2 * d := by
-- proof
  apply StatMech.Universality.zd_nbCount_one d

/--
[zd_nbCount_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_nbCount_bound_eq
  {d n : ℕ} :
-- imply
  zdNBCount d (n + 1) ≤ 2 * d * (2 * d - 1) ^ n := by
-- proof
  apply StatMech.Universality.zd_nbCount_bound d n

/--
[zd_sawCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_sawCount_le_eq
  {d n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  zdSAWCount d n ≤ 2 * d * (2 * d - 1) ^ (n - 1) := by
-- proof
  apply StatMech.Universality.zd_sawCount_le hn

/--
[zd_stepN_part1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_stepN_part1_eq
  {d m n : ℕ}
  {w : Fin (m + n) → ZdStep d}
  {i : ℕ}
-- given
  (hi : i < m) :
-- imply
  zdStepN (zdPart1 (n := n) w) i = zdStepN w i := by
-- proof
  apply StatMech.Universality.zd_stepN_part1 w i hi

/--
[zd_posN_part1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_posN_part1_eq
  {d m n : ℕ}
  {w : Fin (m + n) → ZdStep d}
  {k : ℕ}
-- given
  (hk : k ≤ m) :
-- imply
  zdPos (zdPart1 (n := n) w) k = zdPos w k := by
-- proof
  apply StatMech.Universality.zd_posN_part1 w k hk

/--
[zd_stepN_part2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_stepN_part2_eq
  {d m n : ℕ}
  {w : Fin (m + n) → ZdStep d}
  {i : ℕ} :
-- imply
  zdStepN (zdPart2 (m := m) w) i = zdStepN w (m + i) := by
-- proof
  apply StatMech.Universality.zd_stepN_part2 w i

/--
[zd_posN_part2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_posN_part2_eq
  {d m n : ℕ}
  {w : Fin (m + n) → ZdStep d}
  {k : ℕ} :
-- imply
  zdPos (zdPart2 (m := m) w) k = zdPos w (m + k) - zdPos w m := by
-- proof
  apply StatMech.Universality.zd_posN_part2 w k

/--
[zd_part1_isSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_part1_isSAW_eq
  {d m n : ℕ}
  {w : Fin (m + n) → ZdStep d}
-- given
  (hw : ZdIsSAW w) :
-- imply
  ZdIsSAW (zdPart1 (n := n) w) := by
-- proof
  apply StatMech.Universality.zd_part1_isSAW hw

/--
[zd_part2_isSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_part2_isSAW_eq
  {d m n : ℕ}
  {w : Fin (m + n) → ZdStep d}
-- given
  (hw : ZdIsSAW w) :
-- imply
  ZdIsSAW (zdPart2 (m := m) w) := by
-- proof
  apply StatMech.Universality.zd_part2_isSAW hw

/--
[zd_part_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_part_injective_eq
  {d m n : ℕ} :
-- imply
  Function.Injective (fun w : Fin (m + n) → ZdStep d => (zdPart1 (n := n) w, zdPart2 (m := m) w)) := by
-- proof
  apply StatMech.Universality.zd_part_injective

/--
[zd_sawCount_submult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_sawCount_submult_eq
  {d m n : ℕ} :
-- imply
  zdSAWCount d (m + n) ≤ zdSAWCount d m * zdSAWCount d n := by
-- proof
  apply StatMech.Universality.zd_sawCount_submult d m n

/--
[zd_one_le_sawCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_one_le_sawCount_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  1 ≤ zdSAWCount d n := by
-- proof
  apply StatMech.Universality.zd_one_le_sawCount hd n

/--
[zd_one_le_sawCountR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_one_le_sawCountR_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  1 ≤ zdSAWCountR d n := by
-- proof
  apply StatMech.Universality.zd_one_le_sawCountR hd n

/--
[zd_sawCountR_submult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_sawCountR_submult_eq
  {d : ℕ} :
-- imply
  Submultiplicative (zdSAWCountR d) := by
-- proof
  apply StatMech.Universality.zd_sawCountR_submult d

/--
[zd_connectiveConstant_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_connectiveConstant_exists_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ μ : ℝ, 0 < μ ∧ Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) := by
-- proof
  apply StatMech.Universality.zd_connectiveConstant_exists hd

/--
[zd_le_connectiveConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_le_connectiveConstant_eq
  {d : ℕ}
  {μ : ℝ}
-- given
  (hμ : Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
-- imply
  (d : ℝ) ≤ μ := by
-- proof
  apply StatMech.Universality.zd_le_connectiveConstant hμ

/--
[zd_upperSeq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_upperSeq_tendsto_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n : ℕ => ((2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1)) ^ ((n : ℝ)⁻¹)) atTop (𝓝 (2 * (d : ℝ) - 1)) := by
-- proof
  apply StatMech.Universality.zd_upperSeq_tendsto hd

/--
[zd_connectiveConstant_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_connectiveConstant_le_eq
  {d : ℕ}
  {μ : ℝ}
-- given
  (hd : 1 ≤ d)
  (hμ : Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
-- imply
  μ ≤ 2 * (d : ℝ) - 1 := by
-- proof
  apply StatMech.Universality.zd_connectiveConstant_le hd hμ

/--
[zd_connectiveConstant_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean)
-/
@[path]
private lemma zd_connectiveConstant_bounds_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ μ : ℝ, 0 < μ ∧ Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧ (d : ℝ) ≤ μ ∧ μ ≤ 2 * (d : ℝ) - 1 := by
-- proof
  apply StatMech.Universality.zd_connectiveConstant_bounds hd


-- created on 2026-10-23
