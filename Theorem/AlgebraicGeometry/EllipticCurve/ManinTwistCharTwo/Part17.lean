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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part17
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

lemma super_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      (X ^ Nat.card F) ^ 3 + C W.a₄ * X ^ Nat.card F +
        (X ^ 3 + C W.a₄ * X) := by
  rw [superV_identity W, superH_pow_card W]
  unfold superH
  ring_nf
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination C W.a₆ * htwo

lemma superPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Equation (superPZeroX (F := F))
      (superPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (super_pZero_polynomial_equation W)
  simpa only [superTwist, superPZeroX, superPZeroY, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
