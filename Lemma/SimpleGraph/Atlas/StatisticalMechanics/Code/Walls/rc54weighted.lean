import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc54weighted.Part2
open Finset StatMech StatMech.Walls


/--
[rc54_fwt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_fwt_one_eq
  [Fintype α]
  [DecidableEq α]
  {S : Finset α} :
-- imply
  fwt (fun _ _ => (1 : ℝ)) S = 1 := by
-- proof
  apply StatMech.Walls.rc54_fwt_one S

/--
[rc54_wdpairs_one_eq_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wdpairs_one_eq_dpairsCount_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = (dpairsCount 𝒜 ℬ : ℝ) := by
-- proof
  apply StatMech.Walls.rc54_wdpairs_one_eq_dpairsCount 𝒜 ℬ

/--
[rc54_wdpairs_one_eq_card_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wdpairs_one_eq_card_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = ((boxDoubled 𝒜 ℬ).card : ℝ) := by
-- proof
  apply StatMech.Walls.rc54_wdpairs_one_eq_card_boxDoubled 𝒜 ℬ

/--
[rc54_wdpairs_le_fmarg_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wdpairs_le_fmarg_mul_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.Walls.rc54_wdpairs_le_fmarg_mul hw 𝒜 ℬ

/--
[rc54_wdpairs_add_member_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wdpairs_add_member_le_mul_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  wdpairs w 𝒜 ℬ + w i true * w i true * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.Walls.rc54_wdpairs_add_member_le_mul hw 𝒜 ℬ i

/--
[rc54_wdpairs_fiber_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wdpairs_fiber_recursion_eq
  [Fintype α]
  [DecidableEq α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  wdpairs w 𝒜 ℬ = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) + w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) + w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc54_wdpairs_fiber_recursion w 𝒜 ℬ i

/--
[rc54_wdpairs_one_butterfly_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wdpairs_one_butterfly_invariant_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = ((doubleCompress i (boxDoubled 𝒜 ℬ)).card : ℝ) := by
-- proof
  apply StatMech.Walls.rc54_wdpairs_one_butterfly_invariant i 𝒜 ℬ

/--
[rc54_reflInter_eq_inter_complFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_reflInter_eq_inter_complFam_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ := by
-- proof
  apply StatMech.Walls.rc54_reflInter_eq_inter_complFam 𝒜 ℬ

/--
[rc54_reflInter_card_le_wdpairs_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_reflInter_card_le_wdpairs_one_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  ((rc10_reflInter 𝒜 ℬ).card : ℝ) ≤ wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc54_reflInter_card_le_wdpairs_one 𝒜 ℬ

/--
[rc54_wWt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_wWt_nonneg_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ x b, 0 ≤ rc54_wWt x b := by
-- proof
  apply StatMech.Walls.rc54_wWt_nonneg

/--
[rc54_famCylBox_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_famCylBox_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc20_famCylBox rc54_wA rc54_wB = ({∅} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc54_famCylBox_witness

/--
[rc54_reflInter_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_reflInter_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc10_reflInter rc54_wA rc54_wB = ({{0}} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc54_reflInter_witness

/--
[rc54_fmarg_famCylBox_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_fmarg_famCylBox_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  fmarg rc54_wWt (rc20_famCylBox rc54_wA rc54_wB) = 1 := by
-- proof
  apply StatMech.Walls.rc54_fmarg_famCylBox_witness

/--
[rc54_fmarg_reflInter_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_fmarg_reflInter_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  fmarg rc54_wWt (rc10_reflInter rc54_wA rc54_wB) = 1 / 2 := by
-- proof
  apply StatMech.Walls.rc54_fmarg_reflInter_witness

/--
[rc54_witness_card_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_witness_card_wall_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBox rc54_wA rc54_wB).card ≤ (rc10_reflInter rc54_wA rc54_wB).card := by
-- proof
  apply StatMech.Walls.rc54_witness_card_wall

/--
[rc54_product_weighted_wall_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_product_weighted_wall_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (fmarg rc54_wWt (rc20_famCylBox rc54_wA rc54_wB) ≤ fmarg rc54_wWt (rc10_reflInter rc54_wA rc54_wB)) := by
-- proof
  apply StatMech.Walls.rc54_product_weighted_wall_false

/--
[rc54_exists_product_weight_refuting_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_exists_product_weight_refuting_wall_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ (w : Fin 2 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 2))), (∀ x b, 0 ≤ w x b) ∧ (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card ∧ ¬ (fmarg w (rc20_famCylBox 𝒜 ℬ) ≤ fmarg w (rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc54_exists_product_weight_refuting_wall

/--
[rc54_reimer_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_reimer_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc54_reimer_of_hallDoubled h

/--
[rc54_famCylBoxResidue_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_famCylBoxResidue_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc54_famCylBoxResidue_of_hallDoubled h

/--
[rc54_reimerWprobCore_of_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_reimerWprobCore_of_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc54_reimerWprobCore_of_famCylBoxResidue h

/--
[rc54_reimer_weighted_functional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean)
-/
@[path]
private lemma rc54_reimer_weighted_functional_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = (dpairsCount 𝒜 ℬ : ℝ)) ∧ (∀ (i : Fin 3) (𝒜 ℬ : Finset (Finset (Fin 3))), wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = ((doubleCompress i (boxDoubled 𝒜 ℬ)).card : ℝ)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), ((rc10_reflInter 𝒜 ℬ).card : ℝ) ≤ wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ) ∧ (∃ (w : Fin 2 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 2))), (∀ x b, 0 ≤ w x b) ∧ (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card ∧ ¬ (fmarg w (rc20_famCylBox 𝒜 ℬ) ≤ fmarg w (rc10_reflInter 𝒜 ℬ))) ∧ (rc37_HallDoubled → rc18_CylBoxReflInter) ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc54_reimer_weighted_functional


-- created on 2026-10-23
