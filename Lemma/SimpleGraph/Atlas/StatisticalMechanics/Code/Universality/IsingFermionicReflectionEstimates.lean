import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
open StatMech StatMech.Universality StatMech.Universality.IsingDiagonalWalkHitSplit


/--
[isingLineBinomialKernel_eq_natCard_verticalChoicePath_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma isingLineBinomialKernel_eq_natCard_verticalChoicePath_div_eq
  {t : Nat}
  {x y : Int} :
-- imply
  isingLineBinomialKernel t x y = Nat.card (VerticalChoicePathFamily t x y) / (2 : Real) ^ t := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.isingLineBinomialKernel_eq_natCard_verticalChoicePath_div t x y

/--
[survivalExceptionalFirstHitFamily_code_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalFirstHitFamily_code_injective_eq
  {R : Nat}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int} :
-- imply
  ∃ f : SurvivalExceptionalFirstHitFamily R start level walkLength target → {bits : List (Bool × Bool) // bits.length = walkLength}, Function.Injective f := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalFirstHitFamily_code_injective R start level walkLength target

/--
[natDist_survivingFirstHitFamily_le_exceptions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma natDist_survivingFirstHitFamily_le_exceptions_eq
  {R : Nat}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int} :
-- imply
  Nat.dist (Nat.card (SurvivingFirstHitFamily R start level walkLength target)) (Nat.card (SurvivingFirstHitFamily R (reflectedEndpoint level start) level walkLength target)) ≤ Nat.card (SurvivalExceptionalFirstHitFamily R start level walkLength target) + Nat.card (SurvivalExceptionalMirrorFamily R start level walkLength target) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.natDist_survivingFirstHitFamily_le_exceptions R start level walkLength target

/--
[survivalExceptional_reflected_exists_hit_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptional_reflected_exists_hit_right_eq
  {R : Nat}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int}
  {w : SurvivalExceptionalFirstHitFamily R start level walkLength target}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  ∃ k, k < w.1.1.1.before.length ∧ (isingDiagonalWalkEndpoint (reflectedEndpoint level start) (w.1.1.1.reflectPrefix.steps.take k)).1 = R := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptional_reflected_exists_hit_right R start level walkLength target hstart hlevel hgap w

/--
[survivalExceptionalMirror_reflected_exists_hit_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalMirror_reflected_exists_hit_left_eq
  {R : Nat}
  {start : Int × Int}
  {level : Int}
  {walkLength : Nat}
  {target : Int × Int}
  {w : SurvivalExceptionalMirrorFamily R start level walkLength target}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level) :
-- imply
  ∃ k, k < w.1.1.1.before.length ∧ (isingDiagonalWalkEndpoint start (w.1.1.1.reflectPrefix.steps.take k)).1 = 0 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalMirror_reflected_exists_hit_left R start level walkLength target hstart hlevel w

/--
[survivalExceptionalFirstHitFamily_projection_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalFirstHitFamily_projection_injective_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  Function.Injective (survivalExceptionalProjection R level walkLength start target hstart hlevel hgap) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalFirstHitFamily_projection_injective R level walkLength start target hstart hlevel hgap

/--
[survivalExceptionalProjectionAll_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalProjectionAll_injective_eq
  {R level walkLength : Nat}
  {start : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  Function.Injective (survivalExceptionalProjectionAll R level walkLength start hstart hlevel hgap) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalProjectionAll_injective R level walkLength start hstart hlevel hgap

/--
[natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int) walkLength target) ≤ Nat.card (IsingLineChoicePathFamily (R - level) walkLength (rightGapNeighbor R level hgap) (rightGapLeft R level)) * 2 ^ walkLength := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.natCard_survivalExceptionalFirstHitFamily_le_line_mul_pow R level walkLength start target hstart hlevel hgap

/--
[survivalExceptionalFirstHitFamily_weight_le_inv_rightGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int) walkLength target) : Real) / 4 ^ walkLength ≤ 1 / ((R - level : Nat) : Real) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalFirstHitFamily_weight_le_inv_rightGap R level walkLength start target hstart hlevel hgap

/--
[survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap_eq
  {R level walkLength : Nat}
  {start : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  (Nat.card (SurvivalExceptionalFirstHitFamilyAll R start (level : Int) walkLength) : Real) / 4 ^ walkLength ≤ 1 / ((R - level : Nat) : Real) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalFirstHitFamilyAll_weight_le_inv_rightGap R level walkLength start hstart hlevel hgap

/--
[survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  (Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int) walkLength target) : Real) / 4 ^ walkLength ≤ (1 / ((R - level : Nat) : Real)) * isingLineBinomialKernel walkLength start.2 target.2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalFirstHitFamily_weight_le_inv_rightGap_mul_binomial R level walkLength start target hstart hlevel hgap

/--
[survivalExceptionalMirrorProjection_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalMirrorProjection_injective_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level) :
-- imply
  Function.Injective (survivalExceptionalMirrorProjection R level walkLength start target hstart hlevel) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalMirrorProjection_injective R level walkLength start target hstart hlevel

/--
[survivalExceptionalMirrorProjectionAll_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalMirrorProjectionAll_injective_eq
  {R level walkLength : Nat}
  {start : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level) :
-- imply
  Function.Injective (survivalExceptionalMirrorProjectionAll R level walkLength start hstart hlevel) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalMirrorProjectionAll_injective R level walkLength start hstart hlevel

/--
[survivalExceptionalMirrorFamily_weight_le_inv_leftGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalMirrorFamily_weight_le_inv_leftGap_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level) :
-- imply
  (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int) walkLength target) : Real) / 4 ^ walkLength ≤ 1 / (level : Real) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalMirrorFamily_weight_le_inv_leftGap R level walkLength start target hstart hlevel

/--
[survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap_eq
  {R level walkLength : Nat}
  {start : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level) :
-- imply
  (Nat.card (SurvivalExceptionalMirrorFamilyAll R start (level : Int) walkLength) : Real) / 4 ^ walkLength ≤ 1 / (level : Real) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalMirrorFamilyAll_weight_le_inv_leftGap R level walkLength start hstart hlevel

/--
[survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level) :
-- imply
  (Nat.card (SurvivalExceptionalMirrorFamily R start (level : Int) walkLength target) : Real) / 4 ^ walkLength ≤ (1 / (level : Real)) * isingLineBinomialKernel walkLength start.2 target.2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivalExceptionalMirrorFamily_weight_le_inv_leftGap_mul_binomial R level walkLength start target hstart hlevel

/--
[survivingFirstHitFamily_weight_dist_le_inv_gaps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivingFirstHitFamily_weight_dist_le_inv_gaps_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  (Nat.dist (Nat.card (SurvivingFirstHitFamily R start (level : Int) walkLength target)) (Nat.card (SurvivingFirstHitFamily R (reflectedEndpoint (level : Int) start) (level : Int) walkLength target)) : Real) / 4 ^ walkLength ≤ 1 / ((R - level : Nat) : Real) + 1 / (level : Real) := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivingFirstHitFamily_weight_dist_le_inv_gaps R level walkLength start target hstart hlevel hgap

/--
[survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial_eq
  {R level walkLength : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hlevel : 0 < level)
  (hgap : level + 1 < R) :
-- imply
  (Nat.dist (Nat.card (SurvivingFirstHitFamily R start (level : Int) walkLength target)) (Nat.card (SurvivingFirstHitFamily R (reflectedEndpoint (level : Int) start) (level : Int) walkLength target)) : Real) / 4 ^ walkLength ≤ (1 / ((R - level : Nat) : Real) + 1 / (level : Real)) * isingLineBinomialKernel walkLength start.2 target.2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivingFirstHitFamily_weight_dist_le_inv_gaps_mul_binomial R level walkLength start target hstart hlevel hgap

/--
[survivingFirstHitFamily_diffusive_weight_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean)
-/
@[path]
private lemma survivingFirstHitFamily_diffusive_weight_dist_le_eq
  {R level ρ : Nat}
  {start target : Int × Int}
-- given
  (hstart : start.1 + 1 = level)
  (hρ : 0 < ρ)
  (hleft : ρ + 1 ≤ level)
  (hright : level + 1 + ρ ≤ R) :
-- imply
  (Nat.dist (Nat.card (SurvivingFirstHitFamily R start (level : Int) (ρ * ρ) target)) (Nat.card (SurvivingFirstHitFamily R (reflectedEndpoint (level : Int) start) (level : Int) (ρ * ρ) target)) : Real) / 4 ^ (ρ * ρ) ≤ 4 / (ρ : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.IsingDiagonalWalkHitSplit.survivingFirstHitFamily_diffusive_weight_dist_le R level ρ start target hstart hρ hleft hright


-- created on 2026-10-23
