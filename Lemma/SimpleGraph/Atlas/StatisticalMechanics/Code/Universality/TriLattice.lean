import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.TriLattice
open StatMech StatMech.Universality


/--
[tri_mem_sawWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_mem_sawWalks_eq
  {n : ℕ}
  {w : Fin n → TriStep} :
-- imply
  w ∈ triSAWWalks n ↔ TriIsSAW w := by
-- proof
  apply StatMech.Universality.tri_mem_sawWalks

/--
[tri_mem_nbWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_mem_nbWalks_eq
  {n : ℕ}
  {w : Fin n → TriStep} :
-- imply
  w ∈ triNBWalks n ↔ TriIsNB w := by
-- proof
  apply StatMech.Universality.tri_mem_nbWalks

/--
[triStepVec_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma triStepVec_reverse_eq
  {s : TriStep} :
-- imply
  triStepVec (triReverse s) = - triStepVec s := by
-- proof
  apply StatMech.Universality.triStepVec_reverse s

/--
[triReverse_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma triReverse_reverse_eq
  {s : TriStep} :
-- imply
  triReverse (triReverse s) = s := by
-- proof
  apply StatMech.Universality.triReverse_reverse s

/--
[triReverse_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma triReverse_ne_eq
  {s : TriStep} :
-- imply
  triReverse s ≠ s := by
-- proof
  apply StatMech.Universality.triReverse_ne s

/--
[triPos_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma triPos_succ_eq
  {n : ℕ}
  {w : Fin n → TriStep}
  {k : ℕ} :
-- imply
  triPos w (k + 1) = triPos w k + triStepN w k := by
-- proof
  apply StatMech.Universality.triPos_succ w k

/--
[tri_card_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_card_step_eq :
-- imply
  Fintype.card TriStep = 6 := by
-- proof
  apply StatMech.Universality.tri_card_step

/--
[tri_card_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_card_ne_eq
  {t : TriStep} :
-- imply
  (Finset.univ.filter (fun s : TriStep => s ≠ t)).card = 5 := by
-- proof
  apply StatMech.Universality.tri_card_ne t

/--
[tri_phi_posStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_phi_posStep_eq
  {c : Fin 3} :
-- imply
  1 ≤ triPhi (triStepVec (triPosStep c)) := by
-- proof
  apply StatMech.Universality.tri_phi_posStep c

/--
[triPhi_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma triPhi_add_eq
  {p q : TriSite} :
-- imply
  triPhi (p + q) = triPhi p + triPhi q := by
-- proof
  apply StatMech.Universality.triPhi_add p q

/--
[triPhi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma triPhi_zero_eq :
-- imply
  triPhi (0 : TriSite) = 0 := by
-- proof
  apply StatMech.Universality.triPhi_zero

/--
[tri_phi_pos_wOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_phi_pos_wOf_eq
  {n : ℕ}
  {σ : Fin n → Fin 3}
  {k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  (k : ℤ) ≤ triPhi (triPos (triWOf σ) k) := by
-- proof
  apply StatMech.Universality.tri_phi_pos_wOf σ k hk

/--
[tri_phi_pos_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_phi_pos_strictMono_eq
  {n : ℕ}
  {σ : Fin n → Fin 3}
  {k1 k2 : ℕ}
-- given
  (h12 : k1 < k2)
  (hk2 : k2 ≤ n) :
-- imply
  triPhi (triPos (triWOf σ) k1) < triPhi (triPos (triWOf σ) k2) := by
-- proof
  apply StatMech.Universality.tri_phi_pos_strictMono σ h12 hk2

/--
[tri_isSAW_wOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_isSAW_wOf_eq
  {n : ℕ}
  {σ : Fin n → Fin 3} :
-- imply
  TriIsSAW (triWOf σ) := by
-- proof
  apply StatMech.Universality.tri_isSAW_wOf σ

/--
[tri_posStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_posStep_injective_eq :
-- imply
  Function.Injective triPosStep := by
-- proof
  apply StatMech.Universality.tri_posStep_injective

/--
[tri_wOf_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_wOf_injective_eq
  {n : ℕ} :
-- imply
  Function.Injective (triWOf : (Fin n → Fin 3) → _) := by
-- proof
  apply StatMech.Universality.tri_wOf_injective

/--
[tri_pow_le_sawCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_pow_le_sawCount_eq
  {n : ℕ} :
-- imply
  3 ^ n ≤ triSAWCount n := by
-- proof
  apply StatMech.Universality.tri_pow_le_sawCount

/--
[tri_isSAW_isNB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_isSAW_isNB_eq
  {n : ℕ}
  {w : Fin n → TriStep}
-- given
  (hw : TriIsSAW w) :
-- imply
  TriIsNB w := by
-- proof
  apply StatMech.Universality.tri_isSAW_isNB hw

/--
[tri_sawWalks_subset_nbWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_sawWalks_subset_nbWalks_eq
  {n : ℕ} :
-- imply
  triSAWWalks n ⊆ triNBWalks n := by
-- proof
  apply StatMech.Universality.tri_sawWalks_subset_nbWalks

/--
[tri_dropLast_isNB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_dropLast_isNB_eq
  {n : ℕ}
  {w : Fin (n + 1) → TriStep}
-- given
  (hw : TriIsNB w) :
-- imply
  TriIsNB (triDropLast w) := by
-- proof
  apply StatMech.Universality.tri_dropLast_isNB hw

/--
[tri_fiber_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_fiber_card_le_eq
  {n : ℕ}
  {v : Fin n → TriStep}
-- given
  (hn : 1 ≤ n) :
-- imply
  ({w ∈ triNBWalks (n + 1) | triDropLast w = v}).card ≤ 5 := by
-- proof
  apply StatMech.Universality.tri_fiber_card_le hn v

/--
[tri_nbCount_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_nbCount_succ_le_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  triNBCount (n + 1) ≤ 5 * triNBCount n := by
-- proof
  apply StatMech.Universality.tri_nbCount_succ_le hn

/--
[tri_nbCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_nbCount_one_eq :
-- imply
  triNBCount 1 = 6 := by
-- proof
  apply StatMech.Universality.tri_nbCount_one

/--
[tri_nbCount_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_nbCount_bound_eq
  {n : ℕ} :
-- imply
  triNBCount (n + 1) ≤ 6 * 5 ^ n := by
-- proof
  apply StatMech.Universality.tri_nbCount_bound n

/--
[tri_sawCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_sawCount_le_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  triSAWCount n ≤ 6 * 5 ^ (n - 1) := by
-- proof
  apply StatMech.Universality.tri_sawCount_le hn

/--
[tri_stepN_part1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_stepN_part1_eq
  {m n : ℕ}
  {w : Fin (m + n) → TriStep}
  {i : ℕ}
-- given
  (hi : i < m) :
-- imply
  triStepN (triPart1 (n := n) w) i = triStepN w i := by
-- proof
  apply StatMech.Universality.tri_stepN_part1 w i hi

/--
[tri_posN_part1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_posN_part1_eq
  {m n : ℕ}
  {w : Fin (m + n) → TriStep}
  {k : ℕ}
-- given
  (hk : k ≤ m) :
-- imply
  triPos (triPart1 (n := n) w) k = triPos w k := by
-- proof
  apply StatMech.Universality.tri_posN_part1 w k hk

/--
[tri_stepN_part2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_stepN_part2_eq
  {m n : ℕ}
  {w : Fin (m + n) → TriStep}
  {i : ℕ} :
-- imply
  triStepN (triPart2 (m := m) w) i = triStepN w (m + i) := by
-- proof
  apply StatMech.Universality.tri_stepN_part2 w i

/--
[tri_posN_part2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_posN_part2_eq
  {m n : ℕ}
  {w : Fin (m + n) → TriStep}
  {k : ℕ} :
-- imply
  triPos (triPart2 (m := m) w) k = triPos w (m + k) - triPos w m := by
-- proof
  apply StatMech.Universality.tri_posN_part2 w k

/--
[tri_part1_isSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_part1_isSAW_eq
  {m n : ℕ}
  {w : Fin (m + n) → TriStep}
-- given
  (hw : TriIsSAW w) :
-- imply
  TriIsSAW (triPart1 (n := n) w) := by
-- proof
  apply StatMech.Universality.tri_part1_isSAW hw

/--
[tri_part2_isSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_part2_isSAW_eq
  {m n : ℕ}
  {w : Fin (m + n) → TriStep}
-- given
  (hw : TriIsSAW w) :
-- imply
  TriIsSAW (triPart2 (m := m) w) := by
-- proof
  apply StatMech.Universality.tri_part2_isSAW hw

/--
[tri_part_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_part_injective_eq
  {m n : ℕ} :
-- imply
  Function.Injective (fun w : Fin (m + n) → TriStep => (triPart1 (n := n) w, triPart2 (m := m) w)) := by
-- proof
  apply StatMech.Universality.tri_part_injective

/--
[tri_sawCount_submult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_sawCount_submult_eq
  {m n : ℕ} :
-- imply
  triSAWCount (m + n) ≤ triSAWCount m * triSAWCount n := by
-- proof
  apply StatMech.Universality.tri_sawCount_submult m n

/--
[tri_one_le_sawCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_one_le_sawCount_eq
  {n : ℕ} :
-- imply
  1 ≤ triSAWCount n := by
-- proof
  apply StatMech.Universality.tri_one_le_sawCount n

/--
[tri_one_le_sawCountR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_one_le_sawCountR_eq
  {n : ℕ} :
-- imply
  1 ≤ triSAWCountR n := by
-- proof
  apply StatMech.Universality.tri_one_le_sawCountR n

/--
[tri_sawCountR_submult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_sawCountR_submult_eq :
-- imply
  Submultiplicative triSAWCountR := by
-- proof
  apply StatMech.Universality.tri_sawCountR_submult

/--
[tri_connectiveConstant_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_connectiveConstant_exists_eq :
-- imply
  ∃ κ : ℝ, 0 < κ ∧ Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) := by
-- proof
  apply StatMech.Universality.tri_connectiveConstant_exists

/--
[tri_le_connectiveConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_le_connectiveConstant_eq
  {κ : ℝ}
-- given
  (hκ : Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ)) :
-- imply
  (3 : ℝ) ≤ κ := by
-- proof
  apply StatMech.Universality.tri_le_connectiveConstant hκ

/--
[tri_upperSeq_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_upperSeq_tendsto_eq :
-- imply
  Tendsto (fun n : ℕ => ((6 : ℝ) * (5 : ℝ) ^ (n - 1)) ^ ((n : ℝ)⁻¹)) atTop (𝓝 5) := by
-- proof
  apply StatMech.Universality.tri_upperSeq_tendsto

/--
[tri_connectiveConstant_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_connectiveConstant_le_eq
  {κ : ℝ}
-- given
  (hκ : Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ)) :
-- imply
  κ ≤ 5 := by
-- proof
  apply StatMech.Universality.tri_connectiveConstant_le hκ

/--
[tri_connectiveConstant_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean)
-/
@[path]
private lemma tri_connectiveConstant_bounds_eq :
-- imply
  ∃ κ : ℝ, 0 < κ ∧ Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) ∧ (3 : ℝ) ≤ κ ∧ κ ≤ 5 := by
-- proof
  apply StatMech.Universality.tri_connectiveConstant_bounds


-- created on 2026-10-23
