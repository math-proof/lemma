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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part5
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

lemma exists_mem_charTwoFiber_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    ∃ y, y ^ 2 + b * y = c := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hmod := frobenius_polynomial_mod_quadratic b c
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hbq1, hvalue] at hmod
  simp only [map_one, one_mul, map_zero, add_zero] at hmod
  have hmod' :
      charTwoFrobeniusPolynomial =
        charTwoQuadratic b c *
          frobeniusQuotient b c (charTwoExponent (F := F)) := by
    unfold charTwoFrobeniusPolynomial
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using hmod
  have hdiv : charTwoQuadratic b c ∣
      (charTwoFrobeniusPolynomial : F[X]) :=
    ⟨frobeniusQuotient b c (charTwoExponent (F := F)), hmod'⟩
  have hsplit : (charTwoQuadratic b c).Splits :=
    charTwoFrobeniusPolynomial_splits.of_dvd
      charTwoFrobeniusPolynomial_ne_zero hdiv
  have hnatDegree : (charTwoQuadratic b c).natDegree = 2 := by
    exact (Polynomial.isMonicOfDegree_add_add_two b c).natDegree_eq
  have hdegree : (charTwoQuadratic b c).degree ≠ 0 := by
    apply Polynomial.degree_ne_of_natDegree_ne
    rw [hnatDegree]
    norm_num
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdegree
  refine ⟨y, ?_⟩
  unfold charTwoQuadratic at hy
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
  have hy' : y ^ 2 + b * y = -c := eq_neg_of_add_eq_zero_left hy
  simpa only [CharTwo.neg_eq] using hy'

lemma charTwoFiber_card_eq_two_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    Nat.card (charTwoFiber b c) = 2 := by
  obtain ⟨y, hy⟩ := exists_mem_charTwoFiber_of_value_eq_zero hb hvalue
  exact charTwoFiber_card_eq_two hb hy

lemma charTwoFiber_card_eq_zero_of_value_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = b) :
    Nat.card (charTwoFiber b c) = 0 := by
  apply charTwoFiber_card_eq_zero
  rintro ⟨y, hy⟩
  have hzero := frobeniusValue_eq_zero_of_mem_fiber hb hy
  exact hb (hvalue ▸ hzero)

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
