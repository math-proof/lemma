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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part21
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

lemma super_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (superTwist W).toAffine.Nonsingular x y}
    {hMinus : (superTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (superTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (superTwist W).toAffine.Point) + superQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (superTwist W).toAffine.Point) - superQ W)
    (hdegree : x.denom.natDegree < x.num.natDegree)
    (hdegreeMinus : xMinus.denom.natDegree < xMinus.num.natDegree)
    (hdegreePlus : xPlus.denom.natDegree < xPlus.num.natDegree) :
    xMinus.num.natDegree + xPlus.num.natDegree =
      2 * x.num.natDegree + 2 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X y 0) := hplusEq.1
  have hneg : (superTwist W).toAffine.Nonsingular x
      ((superTwist W).toAffine.negY x y) :=
    ((superTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (superTwist W).toAffine.Point) - superQ W =
    -(-(.some x y hxy : (superTwist W).toAffine.Point) + superQ W) by
      abel] at hminusEq
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X
          ((superTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : xPlus = (y / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxPlus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, superTwist, zero_mul,
      add_zero, sub_eq_add_neg, CharTwo.neg_eq]
  have hrMinus : xMinus =
      ((y + RatFunc.C W.a₃) / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxMinus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      superTwist, zero_mul, add_zero, sub_eq_add_neg,
      CharTwo.neg_eq]
  have heq := super_coordinates_equation W hxy
  have hdiff : RatFunc.X + x ≠ 0 := by
    intro hzero
    apply hxQ
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
  have hpairProd := super_neighbor_pair_product W heq hdiff
  have hpairSum := super_neighbor_pair_sum W (s := y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (superNeighborFirst W x.num x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus * xPlus := by
    rw [superNeighborFirst_ratio]
    calc
      _ = xPlus * xMinus := hpairProd.symm
      _ = xMinus * xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F) (superNeighborSecond W x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus + xPlus := by
    rw [superNeighborSecond_ratio]
    calc
      _ = xPlus + xMinus := hpairSum.symm
      _ = xMinus + xPlus := by ring
  have hpoly : X * x.denom + x.num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := superNeighbor_primitive W
    (RatFunc.isCoprime_num_denom x) hpoly
  have hout : neighborDenominator x.num x.denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := superNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

lemma superD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

lemma superD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
