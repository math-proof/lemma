import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part6
open Finset SimpleGraph Set MeasureTheory StatMech StatMech.Universality


/--
[rlc_affineFlipY_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_zero_eq
  {k : Int}
  {x : Site 2} :
-- imply
  rlc_affineFlipY k x 0 = x 0 := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_zero k x

/--
[rlc_affineFlipY_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_one_eq
  {k : Int}
  {x : Site 2} :
-- imply
  rlc_affineFlipY k x 1 = k - x 1 := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_one k x

/--
[rlc_affineFlipY_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_involutive_eq
  {k : Int}
  {x : Site 2} :
-- imply
  rlc_affineFlipY k (rlc_affineFlipY k x) = x := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_involutive k x

/--
[rlc_adj_affineFlipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_adj_affineFlipY_eq
  {k : Int}
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (rlc_affineFlipY k x) (rlc_affineFlipY k y) := by
-- proof
  apply StatMech.Universality.rlc_adj_affineFlipY k x y

/--
[rlc_affineFlipYEdge_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipYEdge_symm_apply_eq
  {k : Int}
  {e : Sym2 (Site 2)} :
-- imply
  (rlc_affineFlipYEdge k).symm e = e.map (rlc_affineFlipY k) := by
-- proof
  apply StatMech.Universality.rlc_affineFlipYEdge_symm_apply k e

/--
[rlc_affineFlipYConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipYConfig_apply_eq
  {k : Int}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  rlc_affineFlipYConfig k omega e = omega (e.map (rlc_affineFlipY k)) := by
-- proof
  apply StatMech.Universality.rlc_affineFlipYConfig_apply k omega e

/--
[rlc_affineFlipYConfig_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipYConfig_involutive_eq
  {k : Int}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_affineFlipYConfig k (rlc_affineFlipYConfig k omega) = omega := by
-- proof
  apply StatMech.Universality.rlc_affineFlipYConfig_involutive k omega

/--
[rlc_affineFlipYConfig_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipYConfig_measurable_eq
  {k : Int} :
-- imply
  Measurable (rlc_affineFlipYConfig k) := by
-- proof
  apply StatMech.Universality.rlc_affineFlipYConfig_measurable k

/--
[rlc_affineFlipY_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_measurePreserving_eq
  {k : Int}
  {p : NNReal}
-- given
  (hp : p <= 1) :
-- imply
  MeasurePreserving (rlc_affineFlipYConfig k) (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_measurePreserving k p hp

/--
[rlc_mem_rect_affineFlipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_mem_rect_affineFlipY_eq
  {a b c d k : Int}
  {x : Site 2}
-- given
  (hcd : c + d = k) :
-- imply
  x ∈ rect a b c d ↔ rlc_affineFlipY k x ∈ rect a b c d := by
-- proof
  apply StatMech.Universality.rlc_mem_rect_affineFlipY a b c d k hcd x

/--
[rlc_mem_leftSide_affineFlipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_mem_leftSide_affineFlipY_eq
  {a b c d k : Int}
  {x : Site 2}
-- given
  (hcd : c + d = k) :
-- imply
  x ∈ leftSide a b c d ↔ rlc_affineFlipY k x ∈ leftSide a b c d := by
-- proof
  apply StatMech.Universality.rlc_mem_leftSide_affineFlipY a b c d k hcd x

/--
[rlc_mem_rightSide_affineFlipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_mem_rightSide_affineFlipY_eq
  {a b c d k : Int}
  {x : Site 2}
-- given
  (hcd : c + d = k) :
-- imply
  x ∈ rightSide a b c d ↔ rlc_affineFlipY k x ∈ rightSide a b c d := by
-- proof
  apply StatMech.Universality.rlc_mem_rightSide_affineFlipY a b c d k hcd x

/--
[rlc_isOpenEdge_affineFlipY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_isOpenEdge_affineFlipY_eq
  {k : Int}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  IsOpenEdge 2 (rlc_affineFlipYConfig k omega) x y ↔ IsOpenEdge 2 omega (rlc_affineFlipY k x) (rlc_affineFlipY k y) := by
-- proof
  apply StatMech.Universality.rlc_isOpenEdge_affineFlipY k omega x y

/--
[rlc_affineFlipY_lrRestricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_lrRestricted_eq
  {a b c d k : Int}
  {L R : Set (Site 2)}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hcd : c + d = k) :
-- imply
  omega ∈ rlc_lrRestrictedEvent a b c d L R -> rlc_affineFlipYConfig k omega ∈ rlc_lrRestrictedEvent a b c d (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R) := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_lrRestricted a b c d k hcd L R omega

/--
[rlc_affineFlipY_image_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_image_image_eq
  {k : Int}
  {L : Set (Site 2)} :
-- imply
  rlc_affineFlipY k '' (rlc_affineFlipY k '' L) = L := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_image_image k L

/--
[rlc_affineFlipY_lrRestricted_prob_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_lrRestricted_prob_eq_eq
  {a b c d k : Int}
  {L R : Set (Site 2)}
  {p : NNReal}
-- given
  (hcd : c + d = k)
  (hp : p <= 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_lrRestrictedEvent a b c d L R) = (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_lrRestrictedEvent a b c d (rlc_affineFlipY k '' L) (rlc_affineFlipY k '' R)) := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_lrRestricted_prob_eq a b c d k hcd L R p hp

/--
[rlc_affineFlipY_image_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_affineFlipY_image_univ_eq
  {k : Int} :
-- imply
  rlc_affineFlipY k '' (Set.univ : Set (Site 2)) = Set.univ := by
-- proof
  apply StatMech.Universality.rlc_affineFlipY_image_univ k

/--
[rlc_negOneFlip_image_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_negOneFlip_image_upper_eq :
-- imply
  rlc_affineFlipY (-1) '' rlc_upperHalf = rlc_strictLowerHalf := by
-- proof
  apply StatMech.Universality.rlc_negOneFlip_image_upper

/--
[rlc_negOneFlip_image_strictLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_negOneFlip_image_strictLower_eq :
-- imply
  rlc_affineFlipY (-1) '' rlc_strictLowerHalf = rlc_upperHalf := by
-- proof
  apply StatMech.Universality.rlc_negOneFlip_image_strictLower

/--
[rlc_oneFlip_image_strictUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_oneFlip_image_strictUpper_eq :
-- imply
  rlc_affineFlipY 1 '' rlc_strictUpperHalf = rlc_lowerHalf := by
-- proof
  apply StatMech.Universality.rlc_oneFlip_image_strictUpper

/--
[rlc_oneFlip_image_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_oneFlip_image_lower_eq :
-- imply
  rlc_affineFlipY 1 '' rlc_lowerHalf = rlc_strictUpperHalf := by
-- proof
  apply StatMech.Universality.rlc_oneFlip_image_lower

/--
[rlc_lrRestricted_of_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_lrRestricted_of_three_eq
  {a b c d : Int}
  {L R : Set (Site 2)}
-- given
  (hab : a < b)
  (hcd : c < d) :
-- imply
  rlc_lrRestrictedEvent a b c d Set.univ R ∩ rlc_lrRestrictedEvent a b c d L Set.univ ∩ verticalCrossingEvent a b c d ⊆ rlc_lrRestrictedEvent a b c d L R := by
-- proof
  apply StatMech.Universality.rlc_lrRestricted_of_three a b c d hab hcd L R

/--
[rlc_half_localization_of_reflected_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_half_localization_of_reflected_union_eq
  {H A A' : Set (ConfigSpace (Sym2 (Site 2)))}
  {alpha : Real}
-- given
  (hcross : alpha <= rba_selfDualMeasure.real H)
  (hsub : H ⊆ A ∪ A')
  (heq : rba_selfDualMeasure.real A = rba_selfDualMeasure.real A') :
-- imply
  alpha / 2 <= rba_selfDualMeasure.real A := by
-- proof
  apply StatMech.Universality.rlc_half_localization_of_reflected_union H A A' alpha hcross hsub heq

/--
[rlc_insetRightOdd_right_reflection_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOdd_right_reflection_prob_eq
  {n : Int} :
-- imply
  rba_selfDualMeasure.real (rlc_insetRightOddToUpper n) = rba_selfDualMeasure.real (rlc_insetRightOddToStrictLower n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOdd_right_reflection_prob n

/--
[rlc_insetRightOdd_left_reflection_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOdd_left_reflection_prob_eq
  {n : Int} :
-- imply
  rba_selfDualMeasure.real (rlc_insetRightOddStrictLowerToRight n) = rba_selfDualMeasure.real (rlc_insetRightOddUpperToRight n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOdd_left_reflection_prob n

/--
[rlc_insetRightOdd_horizontal_subset_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOdd_horizontal_subset_right_eq
  {n : Int} :
-- imply
  horizontalCrossingEvent 1 (2 * n) (-n) (n - 1) ⊆ rlc_insetRightOddToUpper n ∪ rlc_insetRightOddToStrictLower n := by
-- proof
  apply StatMech.Universality.rlc_insetRightOdd_horizontal_subset_right n

/--
[rlc_insetRightOdd_horizontal_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOdd_horizontal_subset_left_eq
  {n : Int} :
-- imply
  horizontalCrossingEvent 1 (2 * n) (-n) (n - 1) ⊆ rlc_insetRightOddStrictLowerToRight n ∪ rlc_insetRightOddUpperToRight n := by
-- proof
  apply StatMech.Universality.rlc_insetRightOdd_horizontal_subset_left n

/--
[rlc_insetRightOddToUpper_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOddToUpper_half_eq
  {n : Int}
  {alpha : Real}
-- given
  (hcross : alpha <= rba_selfDualMeasure.real (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1))) :
-- imply
  alpha / 2 <= rba_selfDualMeasure.real (rlc_insetRightOddToUpper n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOddToUpper_half n alpha hcross

/--
[rlc_insetRightOddStrictLowerToRight_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOddStrictLowerToRight_half_eq
  {n : Int}
  {alpha : Real}
-- given
  (hcross : alpha <= rba_selfDualMeasure.real (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1))) :
-- imply
  alpha / 2 <= rba_selfDualMeasure.real (rlc_insetRightOddStrictLowerToRight n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOddStrictLowerToRight_half n alpha hcross

/--
[rlc_insetRightOdd_horizontal_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOdd_horizontal_half_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 2 <= rba_selfDualMeasure.real (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOdd_horizontal_half n hn

/--
[rlc_insetRightOdd_vertical_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOdd_vertical_half_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 2 <= rba_selfDualMeasure.real (verticalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOdd_vertical_half n hn

/--
[rlc_insetRightOddSourceCore_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOddSourceCore_mass_lower_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 32 <= rba_selfDualMeasure.real (rlc_insetRightOddSourceCoreEvent n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightOddSourceCore_mass_lower n hn

/--
[rlc_insetLeftOdd_right_reflection_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOdd_right_reflection_prob_eq
  {n : Int} :
-- imply
  rba_selfDualMeasure.real (rlc_insetLeftOddToStrictUpper n) = rba_selfDualMeasure.real (rlc_insetLeftOddToLower n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOdd_right_reflection_prob n

/--
[rlc_insetLeftOdd_left_reflection_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOdd_left_reflection_prob_eq
  {n : Int} :
-- imply
  rba_selfDualMeasure.real (rlc_insetLeftOddLowerToRight n) = rba_selfDualMeasure.real (rlc_insetLeftOddStrictUpperToRight n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOdd_left_reflection_prob n

/--
[rlc_insetLeftOdd_horizontal_subset_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOdd_horizontal_subset_right_eq
  {n : Int} :
-- imply
  horizontalCrossingEvent (-2 * n) (-1) (1 - n) n ⊆ rlc_insetLeftOddToStrictUpper n ∪ rlc_insetLeftOddToLower n := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOdd_horizontal_subset_right n

/--
[rlc_insetLeftOdd_horizontal_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOdd_horizontal_subset_left_eq
  {n : Int} :
-- imply
  horizontalCrossingEvent (-2 * n) (-1) (1 - n) n ⊆ rlc_insetLeftOddLowerToRight n ∪ rlc_insetLeftOddStrictUpperToRight n := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOdd_horizontal_subset_left n

/--
[rlc_insetLeftOddToStrictUpper_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOddToStrictUpper_half_eq
  {n : Int}
  {alpha : Real}
-- given
  (hcross : alpha <= rba_selfDualMeasure.real (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n)) :
-- imply
  alpha / 2 <= rba_selfDualMeasure.real (rlc_insetLeftOddToStrictUpper n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOddToStrictUpper_half n alpha hcross

/--
[rlc_insetLeftOddLowerToRight_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOddLowerToRight_half_eq
  {n : Int}
  {alpha : Real}
-- given
  (hcross : alpha <= rba_selfDualMeasure.real (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n)) :
-- imply
  alpha / 2 <= rba_selfDualMeasure.real (rlc_insetLeftOddLowerToRight n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOddLowerToRight_half n alpha hcross

/--
[rlc_insetLeftOdd_horizontal_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOdd_horizontal_half_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 2 <= rba_selfDualMeasure.real (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOdd_horizontal_half n hn

/--
[rlc_insetLeftOdd_vertical_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOdd_vertical_half_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 2 <= rba_selfDualMeasure.real (verticalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOdd_vertical_half n hn

/--
[rlc_insetLeftOddSourceCore_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOddSourceCore_mass_lower_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 32 <= rba_selfDualMeasure.real (rlc_insetLeftOddSourceCoreEvent n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOddSourceCore_mass_lower n hn

/--
[rlc_insetRightOddSourceCore_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightOddSourceCore_subset_eq
  {n : Int} :
-- imply
  rlc_insetRightOddSourceCoreEvent n ⊆ rlc_insetRightSourceCoreEvent n := by
-- proof
  apply StatMech.Universality.rlc_insetRightOddSourceCore_subset n

/--
[rlc_insetLeftOddSourceCore_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftOddSourceCore_subset_eq
  {n : Int} :
-- imply
  rlc_insetLeftOddSourceCoreEvent n ⊆ rlc_insetLeftSourceCoreEvent n := by
-- proof
  apply StatMech.Universality.rlc_insetLeftOddSourceCore_subset n

/--
[rlc_insetRightSourceCore_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetRightSourceCore_mass_lower_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 32 <= rba_selfDualMeasure.real (rlc_insetRightSourceCoreEvent n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightSourceCore_mass_lower n hn

/--
[rlc_insetLeftSourceCore_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_insetLeftSourceCore_mass_lower_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 32 <= rba_selfDualMeasure.real (rlc_insetLeftSourceCoreEvent n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftSourceCore_mass_lower n hn

/--
[rlc_strictAxisRightSourceEvent_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_strictAxisRightSourceEvent_mass_lower_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 64 <= rba_selfDualMeasure.real (rlc_strictAxisRightSourceEvent n) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisRightSourceEvent_mass_lower n hn

/--
[rlc_strictAxisLeftSourceEvent_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_strictAxisLeftSourceEvent_mass_lower_eq
  {n : Int}
-- given
  (hn : 0 < n) :
-- imply
  (1 : Real) / 64 <= rba_selfDualMeasure.real (rlc_strictAxisLeftSourceEvent n) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisLeftSourceEvent_mass_lower n hn

/--
[rlc_strictAxisStoppedDiagonalEvent_mass_lower_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean)
-/
@[path]
private lemma rlc_strictAxisStoppedDiagonalEvent_mass_lower_unconditional_eq
  {n : Int}
-- given
  (hn : 0 < n)
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  (1 : Real) / 4096 <= rba_selfDualMeasure.real (rlc_strictAxisStoppedDiagonalEvent n) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisStoppedDiagonalEvent_mass_lower_unconditional hn hright hleft


-- created on 2026-10-23
