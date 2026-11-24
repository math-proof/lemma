module
public import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Theorem.Int.EllipticCurve.ManinSequence
public import Theorem.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part15


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
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
    [W.IsCharTwoJEqZeroNF] : (superTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, superTwist_discriminant,
    isUnit_iff_ne_zero]
  apply pow_ne_zero
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  intro hC
  apply ha
  apply RatFunc.C_injective
  simpa using hC

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
