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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part8
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

lemma ordinary_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (X ^ 2 * ordinaryU W) ^ 2 +
        X * X ^ (Nat.card F + 2) * (X ^ 2 * ordinaryU W) =
      (X ^ (Nat.card F + 2)) ^ 3 +
        (X ^ 3 + C W.a₆) * (X ^ (Nat.card F + 2)) ^ 2 +
        C W.a₆ * X ^ 6 := by
  have hu := ordinaryU_identity W
  have hh := ordinaryH_pow_card W
  rw [hh] at hu
  unfold ordinaryH at hu
  have hcancel :
      C W.a₂ * X ^ (2 * Nat.card F + 6) +
        C W.a₂ * X ^ (2 * Nat.card F + 6) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination X ^ 4 * hu + hcancel

lemma ordinaryPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (ordinaryPZeroX (F := F))
      (ordinaryPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (ordinary_pZero_polynomial_equation W)
  simpa only [ordinaryTwist, ordinaryPZeroX, ordinaryPZeroY, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
