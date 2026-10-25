/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part14
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

lemma addition_product_identity (W : WeierstrassCurve F)
    {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) :
    (additionCommon W r - 2 * cubicRat W * s) *
        (additionCommon W r + 2 * cubicRat W * s) =
      symmetricDenominatorRat r * symmetricFirstRat W r := by
  have hsquare :
      (cubicRat W * s) ^ 2 =
        cubicRat W *
          (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 +
            RatFunc.C W.a₄ * r + RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  have hproduct := product_formula
    (RatFunc.C W.a₂) (RatFunc.C W.a₄) (RatFunc.C W.a₆)
      RatFunc.X r 1
  rw [cubicRat_eq] at hsquare
  dsimp only at hproduct
  unfold additionCommon symmetricDenominatorRat symmetricFirstRat
  rw [cubicRat_eq W]
  calc
    _ = ((RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
          2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)) ^ 2 -
        4 * ((RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
          RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * s) ^ 2 := by ring
    _ = _ := by
      rw [hsquare]
      linear_combination hproduct

lemma symmetricOutput_pair_product (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X - r ≠ 0) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      (additionCommon W r - 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 *
        ((additionCommon W r + 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2) := by
  rw [symmetricOutput_zero_ratio]
  unfold symmetricDenominatorRat
  have hproduct := addition_product_identity W heq
  unfold symmetricDenominatorRat at hproduct
  field_simp [hdiff]
  linear_combination -hproduct

lemma paperX_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) -
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  rfl

lemma paperX_neg_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY x y) (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) +
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  rw [paperX_addX_Q_common W hneg hx]
  rw [paperY_negY]
  ring

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
