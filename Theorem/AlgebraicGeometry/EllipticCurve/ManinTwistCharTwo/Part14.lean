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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part15
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

lemma superH_pow_card [Finite F] (W : WeierstrassCurve F) :
    superH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.Polynomial.expand_card F _ fintypeF]
  simp only [superH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

lemma superV_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      superH W ^ Nat.card F + superH W := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  let fintypeF : Fintype F := Fintype.ofFinite F
  have haq : W.a₃ ^ Nat.card F = W.a₃ := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card F _ fintypeF W.a₃
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card_sub_one_eq_one F _ fintypeF W.a₃ ha
  have htail := frobeniusTail_identity (superH W) (C W.a₃)
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hCq : C W.a₃ ^ Nat.card F = C W.a₃ := by rw [← map_pow, haq]
  have hCq1 : C W.a₃ ^ (2 * (Nat.card F - 1)) = 1 := by
    rw [show 2 * (Nat.card F - 1) = (Nat.card F - 1) * 2 by omega,
      pow_mul, ← map_pow, haq1, map_one, one_pow]
  rw [hCq, hCq1, one_mul] at htail
  exact htail

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
