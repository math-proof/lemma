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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part10
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

lemma ordinaryU_derivative [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).derivative =
      frobeniusTail (ordinaryH W) X (charTwoExponent (F := F)) +
        X ^ (Nat.card F + 1) := by
  have hexponent : 0 < charTwoExponent (F := F) := by
    have hcard : 1 < Nat.card F := Finite.one_lt_card
    rw [card_eq_two_pow (F := F)] at hcard
    exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard
  unfold ordinaryU
  rw [derivative_mul, derivative_X,
    derivative_frobeniusTail_ordinary W _ hexponent]
  rw [← card_eq_two_pow (F := F)]
  simp only [one_mul]
  rw [mul_comm, ← pow_succ]

lemma charTwoExponent_pos [Finite F] [CharP F 2] :
    0 < charTwoExponent (F := F) := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  rw [card_eq_two_pow (F := F)] at hcard
  exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard

lemma ordinaryU_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).natDegree =
      1 + 3 * 2 ^ (charTwoExponent (F := F) - 1) := by
  unfold ordinaryU
  have htailDegree := frobeniusTail_ordinary_natDegree W
    (charTwoExponent (F := F)) (charTwoExponent_pos (F := F))
  have htail : frobeniusTail (ordinaryH W) X
      (charTwoExponent (F := F)) ≠ 0 := by
    intro hzero
    rw [hzero] at htailDegree
    simp at htailDegree
  rw [natDegree_mul X_ne_zero htail, natDegree_X, htailDegree]

lemma ordinaryMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk]
    rw [pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hU : (ordinaryU W).natDegree ≤ 2 * Nat.card F := by
    rw [ordinaryU_natDegree W]
    change 1 + 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have hfirst : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    have hsecond : (X ^ (Nat.card F + 1) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hfirst hsecond)) hU)
  have heq : ordinaryMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold ordinaryMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

lemma eval_derivative_ordinaryMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) (x : F) :
    (ordinaryMinusOneNumerator W).derivative.eval x =
      x + frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
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
  have hcoeff3 : (((Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  have hexponent3 : Nat.card F + 1 - 1 = Nat.card F := by omega
  unfold ordinaryMinusOneNumerator
  simp only [derivative_add, derivative_pow, derivative_X,
    ordinaryU_derivative, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_one, eval_frobeniusTail, hcoeff1, hcoeff2, hcoeff3, one_mul,
    zero_mul, hexponent1, hexponent3, hx2q, hxq, hxq1]
  have hcancel : x ^ 2 + x ^ 2 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

lemma ordinaryTailValue_zero_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    frobeniusValue ((ordinaryH W).eval 0) 0
      (charTwoExponent (F := F)) ≠ 0 := by
  rw [frobeniusValue_zero_coefficient _ _ (charTwoExponent_pos (F := F))]
  simp only [ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C,
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_add]
  exact pow_ne_zero _ (ordinary_a₆_ne_zero W)

lemma ordinaryEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 + x * y = (ordinaryH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₃_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₄_of_isCharTwoJNeZeroNF, one_mul, zero_mul,
    add_zero, ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
