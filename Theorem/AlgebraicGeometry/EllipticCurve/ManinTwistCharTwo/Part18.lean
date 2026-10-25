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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part18
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

lemma superV_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superV W).natDegree = 3 * 2 ^ (charTwoExponent (F := F) - 1) :=
  frobeniusTail_super_natDegree W _ (charTwoExponent_pos (F := F))

lemma superMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk, pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hV : (superV W).natDegree ≤ 2 * Nat.card F := by
    rw [superV_natDegree W]
    change 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have h₁ : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by rw [natDegree_X_pow]; omega
    have h₂ : (C W.a₄ * (X ^ Nat.card F + X)).natDegree ≤
        2 * Nat.card F := by
      calc
        _ ≤ (X ^ Nat.card F + X : F[X]).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ ≤ max (Nat.card F) 1 := by
          exact (natDegree_add_le _ _).trans (max_le
            (by rw [natDegree_X_pow]; exact le_max_left _ _)
            (by rw [natDegree_X]; exact le_max_right _ _))
        _ ≤ 2 * Nat.card F := by omega
    have h₃ : (C W.a₃ * superV W).natDegree ≤ 2 * Nat.card F :=
      (Polynomial.natDegree_C_mul_le _ _).trans hV
    have h₄ : (C (W.a₃ ^ 2) : F[X]).natDegree ≤ 2 * Nat.card F := by
      rw [natDegree_C]
      omega
    dsimp only [remainder]
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le h₁ h₂)) h₃)) h₄)
  have heq : superMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold superMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

lemma superEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔
      y ^ 2 + W.a₃ * y = (superH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJEqZeroNF,
    WeierstrassCurve.a₂_of_isCharTwoJEqZeroNF, zero_mul, add_zero,
    superH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
