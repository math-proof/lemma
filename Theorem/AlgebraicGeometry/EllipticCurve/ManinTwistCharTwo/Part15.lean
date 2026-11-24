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
public import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part16


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

lemma superTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) : (superTwist W).Δ = RatFunc.C W.a₃ ^ 4 := by
  simp only [superTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, sub_zero, CharTwo.neg_eq]
  ring_nf
  rw [CharTwo.neg_eq]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
