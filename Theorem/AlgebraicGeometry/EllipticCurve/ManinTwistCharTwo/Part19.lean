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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part19
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

lemma superX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0) =
      algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne superPZeroX_ne_QX]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superPZeroX, superPZeroY, zero_mul, add_zero,
    sub_eq_add_neg, CharTwo.neg_eq]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [superMinusOneNumerator, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hL : (RatFunc.X ^ Nat.card F + RatFunc.X : RatFunc F) ≠ 0 := by
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hv := congrArg (algebraMap F[X] (RatFunc F)) (superV_identity W)
  rw [superH_pow_card W] at hv
  simp only [superH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hv
  field_simp [hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hv +
    ((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃ +
      RatFunc.X ^ (Nat.card F * 3) + RatFunc.C W.a₄ *
        RatFunc.X ^ Nat.card F + RatFunc.C W.a₆ + RatFunc.X ^ 3 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * htwo +
    (-((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃) +
      RatFunc.X * RatFunc.X ^ (Nat.card F * 2) -
      RatFunc.X * RatFunc.C W.a₄ +
      RatFunc.X ^ 2 * RatFunc.X ^ Nat.card F -
      RatFunc.X ^ Nat.card F * RatFunc.C W.a₄ - RatFunc.C W.a₆) * htwo

lemma superPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∃ y hxy, superPoint W (-1) =
      .some
        ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
            ((superTwist W).toAffine.negY (superPZeroX (F := F))
              (superPZeroY W)) 0)) y hxy := by
  have hp : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F)) (superPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superPZero_equation W)
  have hneg : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F))
      ((superTwist W).toAffine.negY (superPZeroX (F := F))
        (superPZeroY W)) :=
    ((superTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -superPZero W = .some (superPZeroX (F := F))
        ((superTwist W).toAffine.negY (superPZeroX (F := F))
          (superPZeroY W)) hneg := by
    rw [show superPZero W =
      .some (superPZeroX (F := F)) (superPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) superPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superQ_equation W))
  rw [← hnegP, ← show superQ W = .some RatFunc.X 0 _ from rfl] at hadd
  have hpoint : superPoint W (-1) = -(-superPZero W + superQ W) := by
    unfold superPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

lemma eval_derivative_superMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] (x : F) :
    (superMinusOneNumerator W).derivative.eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one W.a₃ ha
  have hcard : 2 ≤ Nat.card F := Finite.one_lt_card
  have hamul : W.a₃ * W.a₃ ^ (Nat.card F - 2) = 1 := by
    calc
      W.a₃ * W.a₃ ^ (Nat.card F - 2) =
          W.a₃ ^ (Nat.card F - 2 + 1) := (pow_succ' _ _).symm
      _ = W.a₃ ^ (Nat.card F - 1) := by congr 1; omega
      _ = 1 := haq1
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  unfold superMinusOneNumerator superV
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [derivative_frobeniusTail_super W _ (charTwoExponent_pos (F := F))]
  rw [← card_eq_two_pow (F := F)]
  simp only [derivative_pow, derivative_X, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, eval_one, hcoeff1, hcoeff2, one_mul, zero_mul,
    hexponent1, hx2q, hqcast, add_zero]
  rw [← mul_assoc, hamul, one_mul]
  simp only [mul_one, zero_add]
  exact CharTwo.add_self_eq_zero (x ^ 2 + W.a₄)

lemma superMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : superMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := superMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

lemma superNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F)
    (hvalue : frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) = W.a₃) :
    (X - C x) ^ 2 ∣ superMinusOneNumerator W := by
  have hN := superMinusOneNumerator_ne_zero W
  have hroot : (superMinusOneNumerator W).IsRoot x := by
    change (superMinusOneNumerator W).eval x = 0
    rw [eval_superMinusOneNumerator, hvalue]
    simpa only [pow_two] using
      CharTwo.add_self_eq_zero (W.a₃ * W.a₃)
  have hderivativeRoot : (superMinusOneNumerator W).derivative.IsRoot x := by
    exact eval_derivative_superMinusOneNumerator W x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
