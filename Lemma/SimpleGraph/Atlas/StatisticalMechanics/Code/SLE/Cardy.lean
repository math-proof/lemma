import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.Cardy
open Complex Filter Topology StatMech StatMech.SLE


/--
[crossRatio_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma crossRatio_def_eq
  [Field K]
  {z₁ z₂ z₃ z₄ : K} :
-- imply
  crossRatio z₁ z₂ z₃ z₄ = (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃)) := by
-- proof
  apply StatMech.SLE.crossRatio_def z₁ z₂ z₃ z₄

/--
[crossRatio_self_left_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma crossRatio_self_left_third_eq
  [Field K]
  {z z₂ z₄ : K} :
-- imply
  crossRatio z z₂ z z₄ = 0 := by
-- proof
  apply StatMech.SLE.crossRatio_self_left_third z z₂ z₄

/--
[crossRatio_self_second_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma crossRatio_self_second_fourth_eq
  [Field K]
  {z₁ z z₃ : K} :
-- imply
  crossRatio z₁ z z₃ z = 0 := by
-- proof
  apply StatMech.SLE.crossRatio_self_second_fourth z₁ z z₃

/--
[crossRatio_eq_one_of_third_eq_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma crossRatio_eq_one_of_third_eq_fourth_eq
  [Field K]
  {z₁ z₂ z₃ z₄ : K}
-- given
  (h : z₃ = z₄)
  (h₁ : z₁ - z₄ ≠ 0)
  (h₂ : z₂ - z₃ ≠ 0) :
-- imply
  crossRatio z₁ z₂ z₃ z₄ = 1 := by
-- proof
  apply StatMech.SLE.crossRatio_eq_one_of_third_eq_fourth h h₁ h₂

/--
[Mobius.id_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma id_apply_eq
  [Field K]
  {z : K} :
-- imply
  (Mobius.id K).apply z = z := by
-- proof
  apply StatMech.SLE.Mobius.id_apply z

/--
[crossRatio_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma crossRatio_translation_invariant_eq
  [Field K]
  {t z₁ z₂ z₃ z₄ : K} :
-- imply
  crossRatio (z₁ + t) (z₂ + t) (z₃ + t) (z₄ + t) = crossRatio z₁ z₂ z₃ z₄ := by
-- proof
  apply StatMech.SLE.crossRatio_translation_invariant t z₁ z₂ z₃ z₄

/--
[crossRatio_scaling_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma crossRatio_scaling_invariant_eq
  [Field K]
  {s : K}
  {z₁ z₂ z₃ z₄ : K}
-- given
  (hs : s ≠ 0) :
-- imply
  crossRatio (s * z₁) (s * z₂) (s * z₃) (s * z₄) = crossRatio z₁ z₂ z₃ z₄ := by
-- proof
  apply StatMech.SLE.crossRatio_scaling_invariant hs z₁ z₂ z₃ z₄

/--
[cardyPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma cardyPrefactor_pos_eq :
-- imply
  0 < cardyPrefactor := by
-- proof
  apply StatMech.SLE.cardyPrefactor_pos

/--
[cardyCrossing_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma cardyCrossing_zero_eq :
-- imply
  cardyCrossing 0 = 0 := by
-- proof
  apply StatMech.SLE.cardyCrossing_zero

/--
[sle_phase_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma sle_phase_trichotomy_eq
  {κ : ℝ}
-- given
  (hκ : 0 ≤ κ) :
-- imply
  IsSimplePhase κ ∨ IsSelfTouchingPhase κ ∨ IsSpaceFillingPhase κ := by
-- proof
  apply StatMech.SLE.sle_phase_trichotomy hκ

/--
[not_simple_and_selfTouching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma not_simple_and_selfTouching_eq
  {κ : ℝ}
-- given
  (h : IsSimplePhase κ) :
-- imply
  ¬ IsSelfTouchingPhase κ := by
-- proof
  apply StatMech.SLE.not_simple_and_selfTouching h

/--
[not_selfTouching_and_spaceFilling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma not_selfTouching_and_spaceFilling_eq
  {κ : ℝ}
-- given
  (h : IsSelfTouchingPhase κ) :
-- imply
  ¬ IsSpaceFillingPhase κ := by
-- proof
  apply StatMech.SLE.not_selfTouching_and_spaceFilling h

/--
[sleDimension_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma sleDimension_apply_eq
  {κ : ℝ} :
-- imply
  sleDimension κ = 1 + κ / 8 := by
-- proof
  apply StatMech.SLE.sleDimension_apply κ

/--
[sleDimension_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma sleDimension_zero_eq :
-- imply
  sleDimension 0 = 1 := by
-- proof
  apply StatMech.SLE.sleDimension_zero

/--
[sleDimension_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma sleDimension_eight_eq :
-- imply
  sleDimension 8 = 2 := by
-- proof
  apply StatMech.SLE.sleDimension_eight

/--
[sleDimension_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma sleDimension_mem_Icc_eq
  {κ : ℝ}
-- given
  (h0 : 0 ≤ κ)
  (h8 : κ ≤ 8) :
-- imply
  sleDimension κ ∈ Set.Icc (1 : ℝ) 2 := by
-- proof
  apply StatMech.SLE.sleDimension_mem_Icc h0 h8

/--
[sleDimension_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma sleDimension_strictMono_eq :
-- imply
  StrictMono sleDimension := by
-- proof
  apply StatMech.SLE.sleDimension_strictMono

/--
[kappaPercolation_selfTouching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma kappaPercolation_selfTouching_eq :
-- imply
  IsSelfTouchingPhase kappaPercolation := by
-- proof
  apply StatMech.SLE.kappaPercolation_selfTouching

/--
[kappaIsing_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma kappaIsing_simple_eq :
-- imply
  IsSimplePhase kappaIsing := by
-- proof
  apply StatMech.SLE.kappaIsing_simple

/--
[kappaFKIsing_selfTouching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma kappaFKIsing_selfTouching_eq :
-- imply
  IsSelfTouchingPhase kappaFKIsing := by
-- proof
  apply StatMech.SLE.kappaFKIsing_selfTouching

/--
[centralCharge_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma centralCharge_percolation_eq :
-- imply
  centralCharge kappaPercolation = 0 := by
-- proof
  apply StatMech.SLE.centralCharge_percolation

/--
[centralCharge_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma centralCharge_ising_eq :
-- imply
  centralCharge kappaIsing = 1 / 2 := by
-- proof
  apply StatMech.SLE.centralCharge_ising

/--
[IsCLEParameter.pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma pos_eq
  {κ : ℝ}
-- given
  (h : IsCLEParameter κ) :
-- imply
  0 < κ := by
-- proof
  apply StatMech.SLE.IsCLEParameter.pos h

/--
[IsCLE.kappa_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean)
-/
@[path]
private lemma kappa_pos_eq
  [MeasurableSpace Ω]
  {κ : ℝ}
  {loops : Ω → Set (Set ℂ)}
  {μ : MeasureTheory.Measure Ω}
-- given
  (h : IsCLE κ loops μ) :
-- imply
  0 < κ := by
-- proof
  apply StatMech.SLE.IsCLE.kappa_pos h


-- created on 2026-10-23
