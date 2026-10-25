/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part13
/-!
# Manin's elementary proof in characteristic two

This file packages the ordinary and supersingular normal-form cases, following
Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).
-/


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

noncomputable section

open Polynomial

open scoped CharTwo

open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

universe u

variable {F : Type u} [Field F]

lemma ordinary_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
    {hMinus : (ordinaryTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (ordinaryTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X ^ 3)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W)
    (hdegree : (ordinaryPaperX x).denom.natDegree <
      (ordinaryPaperX x).num.natDegree)
    (hdegreeMinus : (ordinaryPaperX xMinus).denom.natDegree <
      (ordinaryPaperX xMinus).num.natDegree)
    (hdegreePlus : (ordinaryPaperX xPlus).denom.natDegree <
      (ordinaryPaperX xPlus).num.natDegree) :
    (ordinaryPaperX xMinus).num.natDegree +
        (ordinaryPaperX xPlus).num.natDegree =
      2 * (ordinaryPaperX x).num.natDegree + 2 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0) :=
    hplusEq.1
  have hneg : (ordinaryTwist W).toAffine.Nonsingular x
      ((ordinaryTwist W).toAffine.negY x y) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W =
    -(-(.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W) by
      abel] at hminusEq
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : ordinaryPaperX xPlus =
      (ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxPlus]
    exact ordinaryPaperX_addX_Q_eq W hxQ
  have hrMinus : ordinaryPaperX xMinus =
      ((ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        (ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X) +
            RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxMinus, ordinaryPaperX_addX_Q_eq W hxQ,
      ordinaryPaperY_negY W]
  have heq := ordinary_paper_coordinates_equation W hxy
  have hdiff : RatFunc.X + ordinaryPaperX x ≠ 0 := by
    intro hzero
    apply hxQ
    have hr : ordinaryPaperX x = RatFunc.X := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
    unfold ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hpairProd := ordinary_neighbor_pair_product W heq hdiff
  have hpairSum := ordinary_neighbor_pair_sum W
    (s := ordinaryPaperY y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborFirst W (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus * ordinaryPaperX xPlus := by
    rw [ordinaryNeighborFirst_ratio]
    calc
      _ = ordinaryPaperX xPlus * ordinaryPaperX xMinus := hpairProd.symm
      _ = ordinaryPaperX xMinus * ordinaryPaperX xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborSecond (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus + ordinaryPaperX xPlus := by
    rw [ordinaryNeighborSecond_ratio]
    calc
      _ = ordinaryPaperX xPlus + ordinaryPaperX xMinus := hpairSum.symm
      _ = ordinaryPaperX xMinus + ordinaryPaperX xPlus := by ring
  have hpoly : X * (ordinaryPaperX x).denom + (ordinaryPaperX x).num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := ordinaryNeighbor_primitive W
    (RatFunc.isCoprime_num_denom (ordinaryPaperX x)) hpoly
  have hout : neighborDenominator (ordinaryPaperX x).num
      (ordinaryPaperX x).denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := ordinaryNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

lemma ordinaryD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

lemma ordinaryD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
