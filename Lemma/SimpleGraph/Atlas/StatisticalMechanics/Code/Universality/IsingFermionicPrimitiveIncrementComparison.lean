import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIncrementComparison
open Filter Set Topology StatMech StatMech.Universality


/--
[norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_eq
  {a v : Complex}
  {B epsilon : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hepsilon : 0 <= epsilon)
  (hbound : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v)) <= B)
  (hosc : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v) - f a) <= epsilon) :
-- imply
  norm (complexDisplacementIntegral (fun z => f z ^ 2) a v - f a ^ 2 * v) <= (2 * B * epsilon) * norm v := by
-- proof
  apply StatMech.Universality.norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le f hf a v B epsilon hepsilon hbound hosc

/--
[norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_lipschitz_eq
  {a v : Complex}
  {B L : NNReal}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hbound : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v)) <= B)
  (hlip : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v) - f a) <= (L : Real) * norm ((t : Complex) * v)) :
-- imply
  norm (complexDisplacementIntegral (fun z => f z ^ 2) a v - f a ^ 2 * v) <= (2 * (B : Real) * (L : Real) * norm v) * norm v := by
-- proof
  apply StatMech.Universality.norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_lipschitz f hf a v B L hbound hlip

/--
[norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_closedBall_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_closedBall_anchor_eq
  {a v : Complex}
  {A R : Real}
  {L : NNReal}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hR : 0 <= R)
  (hanchor : norm (f 0) <= A)
  (hlip : LipschitzOnWith L f (Metric.closedBall (0 : Complex) R))
  (ha : a ∈ Metric.closedBall (0 : Complex) R)
  (hsegment : forall t : Real, t ∈ Icc 0 1 -> a + (t : Complex) * v ∈ Metric.closedBall (0 : Complex) R) :
-- imply
  norm (complexDisplacementIntegral (fun z => f z ^ 2) a v - f a ^ 2 * v) <= (2 * (A + (L : Real) * R) * ((L : Real) * norm v)) * norm v := by
-- proof
  apply StatMech.Universality.norm_complexDisplacementIntegral_sq_sub_start_sq_mul_le_of_closedBall_anchor f hf a v A R L hR hanchor hlip ha hsegment

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_segmentSquareIntegral_sub_start_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_segmentSquareIntegral_sub_start_le_eq
  {k : Nat}
  {R : Real}
  {A : Real}
  {a v : Complex}
-- given
  (hR : 0 <= R)
  (hk : 2 <= k)
  (hwide : 2 * R + ((((k / 2) * (k + 1) : Nat) : Real) + 6) * fkIsingExpandingSquareScale k <= fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
  (hanchor : norm (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0) <= A)
  (ha : a ∈ Metric.closedBall (0 : Complex) R)
  (hsegment : forall t : Real, t ∈ Icc 0 1 -> a + (t : Complex) * v ∈ Metric.closedBall (0 : Complex) R) :
-- imply
  norm (complexDisplacementIntegral (fun z => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k z ^ 2) a v - fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k a ^ 2 * v) <= (2 * (A + 9728 * R) * (9728 * norm v)) * norm v := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_segmentSquareIntegral_sub_start_le k R hR hk hwide A hanchor a v ha hsegment

/--
[exists_centeredReflectedInterpolant_segmentSquareIntegral_error_of_root_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma exists_centeredReflectedInterpolant_segmentSquareIntegral_error_of_root_tendsto_eq
  {rootLimit : Complex}
  {R : Real}
-- given
  (hroot : Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0) atTop (nhds rootLimit))
  (hR : 0 <= R)
  (a v : Nat -> Complex)
  (hv : Tendsto (fun k => norm (v k)) atTop (nhds 0))
  (hwide : ∀ᶠ k in atTop, 2 * R + ((((k / 2) * (k + 1) : Nat) : Real) + 6) * fkIsingExpandingSquareScale k <= fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k)
  (ha : ∀ᶠ k in atTop, a k ∈ Metric.closedBall (0 : Complex) R)
  (hsegment : ∀ᶠ k in atTop, forall t : Real, t ∈ Icc 0 1 -> a k + (t : Complex) * v k ∈ Metric.closedBall (0 : Complex) R) :
-- imply
  exists error : Nat -> Real, (forall k, 0 <= error k) /\ Tendsto error atTop (nhds 0) /\ (∀ᶠ k in atTop, norm (complexDisplacementIntegral (fun z => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k z ^ 2) (a k) (v k) - fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k (a k) ^ 2 * v k) <= error k * norm (v k)) := by
-- proof
  apply StatMech.Universality.exists_centeredReflectedInterpolant_segmentSquareIntegral_error_of_root_tendsto rootLimit hroot R hR a v hv hwide ha hsegment

/--
[norm_complexDisplacementIntegral_sq_sub_realIncrement_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma norm_complexDisplacementIntegral_sq_sub_realIncrement_le_eq
  {a v : Complex}
  {B epsilon increment : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hepsilon : 0 <= epsilon)
  (hbound : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v)) <= B)
  (hosc : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v) - f a) <= epsilon)
  (hexact : f a ^ 2 * v = (increment : Complex)) :
-- imply
  norm (complexDisplacementIntegral (fun z => f z ^ 2) a v - (increment : Complex)) <= (2 * B * epsilon) * norm v := by
-- proof
  apply StatMech.Universality.norm_complexDisplacementIntegral_sq_sub_realIncrement_le f hf a v B epsilon increment hepsilon hbound hosc hexact

/--
[abs_complexDisplacementIntegral_sq_im_sub_realIncrement_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma abs_complexDisplacementIntegral_sq_im_sub_realIncrement_le_eq
  {a v : Complex}
  {B epsilon increment : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hepsilon : 0 <= epsilon)
  (hbound : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v)) <= B)
  (hosc : forall t : Real, t ∈ Icc 0 1 -> norm (f (a + (t : Complex) * v) - f a) <= epsilon)
  (hexact : (f a ^ 2 * v).im = increment) :
-- imply
  abs ((complexDisplacementIntegral (fun z => f z ^ 2) a v).im - increment) <= (2 * B * epsilon) * norm v := by
-- proof
  apply StatMech.Universality.abs_complexDisplacementIntegral_sq_im_sub_realIncrement_le f hf a v B epsilon increment hepsilon hbound hosc hexact

/--
[normSq_isingProj_one_sub_negOne_eq_sq_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma normSq_isingProj_one_sub_negOne_eq_sq_re_eq
  {z : Complex} :
-- imply
  Complex.normSq (isingProj 1 z) - Complex.normSq (isingProj (-1) z) = (z ^ 2).re := by
-- proof
  apply StatMech.Universality.normSq_isingProj_one_sub_negOne_eq_sq_re z

/--
[normSq_isingProj_negI_sub_I_eq_sq_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma normSq_isingProj_negI_sub_I_eq_sq_im_eq
  {z : Complex} :
-- imply
  Complex.normSq (isingProj (-Complex.I) z) - Complex.normSq (isingProj Complex.I z) = (z ^ 2).im := by
-- proof
  apply StatMech.Universality.normSq_isingProj_negI_sub_I_eq_sq_im z

/--
[normSq_isingProj_one_sub_negI_eq_sq_mul_northwest_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma normSq_isingProj_one_sub_negI_eq_sq_mul_northwest_im_eq
  {z : Complex} :
-- imply
  Complex.normSq (isingProj 1 z) - Complex.normSq (isingProj (-Complex.I) z) = (z ^ 2 * ((-1 + Complex.I) / 2)).im := by
-- proof
  apply StatMech.Universality.normSq_isingProj_one_sub_negI_eq_sq_mul_northwest_im z

/--
[normSq_isingProj_one_sub_I_eq_sq_mul_northeast_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma normSq_isingProj_one_sub_I_eq_sq_mul_northeast_im_eq
  {z : Complex} :
-- imply
  Complex.normSq (isingProj 1 z) - Complex.normSq (isingProj Complex.I z) = (z ^ 2 * ((1 + Complex.I) / 2)).im := by
-- proof
  apply StatMech.Universality.normSq_isingProj_one_sub_I_eq_sq_mul_northeast_im z

/--
[normSq_isingProj_negI_sub_negOne_eq_sq_mul_northeast_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIncrementComparison.lean)
-/
@[path]
private lemma normSq_isingProj_negI_sub_negOne_eq_sq_mul_northeast_im_eq
  {z : Complex} :
-- imply
  Complex.normSq (isingProj (-Complex.I) z) - Complex.normSq (isingProj (-1) z) = (z ^ 2 * ((1 + Complex.I) / 2)).im := by
-- proof
  apply StatMech.Universality.normSq_isingProj_negI_sub_negOne_eq_sq_mul_northeast_im z


-- created on 2026-10-23
