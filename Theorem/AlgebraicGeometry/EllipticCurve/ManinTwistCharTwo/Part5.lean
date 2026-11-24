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
public import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part6


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

lemma ordinaryH_pow_card [Finite F] (W : WeierstrassCurve F) :
    ordinaryH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.Polynomial.expand_card F _ fintypeF]
  simp only [ordinaryH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

lemma ordinaryU_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryU W ^ 2 + X ^ (Nat.card F + 1) * ordinaryU W =
      X ^ 2 * ordinaryH W ^ Nat.card F + X ^ (2 * Nat.card F) * ordinaryH W := by
  have htail := frobeniusTail_identity (ordinaryH W) X
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  have hterm :
      X ^ 2 * (X ^ (2 * (Nat.card F - 1)) * ordinaryH W) =
        X ^ (2 * Nat.card F) * ordinaryH W := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  unfold ordinaryU
  calc
    (X * frobeniusTail (ordinaryH W) X charTwoExponent) ^ 2 +
        X ^ (Nat.card F + 1) *
          (X * frobeniusTail (ordinaryH W) X charTwoExponent) =
      X ^ 2 * (frobeniusTail (ordinaryH W) X charTwoExponent ^ 2 +
        X ^ Nat.card F * frobeniusTail (ordinaryH W) X charTwoExponent) := by
          ring
    _ = X ^ 2 * (ordinaryH W ^ Nat.card F +
        X ^ (2 * (Nat.card F - 1)) * ordinaryH W) := by rw [htail]
    _ = _ := by rw [mul_add, hterm]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
