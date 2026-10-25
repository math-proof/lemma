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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part4
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

lemma frobeniusValue_eq_zero_of_mem_fiber [Finite F] [CharP F 2]
    {b c y : F} (hb : b ≠ 0) (hy : y ^ 2 + b * y = c) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hyq : y ^ Nat.card F = y := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card y
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have h := frobenius_pow_eq_linear_add_value hy
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hyq, hbq1, one_mul] at h
  have hzero : (0 : F) = frobeniusValue c b (charTwoExponent (F := F)) :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hzero.symm

lemma frobeniusValue_eq_zero_or_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 ∨
      frobeniusValue c b (charTwoExponent (F := F)) = b := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq : b ^ Nat.card F = b := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card b
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hcq : c ^ Nat.card F = c := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card c
  have htail := congrArg (Polynomial.eval (0 : F))
    (frobeniusTail_identity (C c) (C b) (charTwoExponent (F := F)))
  simp only [eval_add, eval_mul, eval_pow, eval_C] at htail
  rw [eval_frobeniusTail, eval_C, eval_C,
    ← card_eq_two_pow (F := F), hbq, hcq] at htail
  rw [show b ^ (2 * (Nat.card F - 1)) = 1 by
    rw [mul_comm, pow_mul, hbq1, one_pow], one_mul] at htail
  rw [CharTwo.add_self_eq_zero] at htail
  have hfactor :
      frobeniusValue c b (charTwoExponent (F := F)) *
        (frobeniusValue c b (charTwoExponent (F := F)) + b) = 0 := by
    calc
      _ = frobeniusValue c b (charTwoExponent (F := F)) ^ 2 +
          b * frobeniusValue c b (charTwoExponent (F := F)) := by ring
      _ = 0 := htail
  rcases mul_eq_zero.mp hfactor with hzero | heq
  · exact Or.inl hzero
  · exact Or.inr (by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left heq)

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
