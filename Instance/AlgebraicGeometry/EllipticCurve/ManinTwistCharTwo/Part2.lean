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
import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part6
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

instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, ordinaryTwist_discriminant,
    isUnit_iff_ne_zero]
  apply mul_ne_zero
  · have hb : W.a₆ ≠ 0 := by
      have h := W.Δ'.ne_zero
      rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
      exact h
    intro hC
    apply hb
    apply RatFunc.C_injective
    simpa using hC
  · exact pow_ne_zero 12 RatFunc.X_ne_zero

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
