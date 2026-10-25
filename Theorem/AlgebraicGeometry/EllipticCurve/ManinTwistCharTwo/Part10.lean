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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part11
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

lemma ordinaryMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : ordinaryMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := ordinaryMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

lemma rootMultiplicity_ordinaryNumerator_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) = 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot 0 := by
    change (ordinaryMinusOneNumerator W).eval 0 = 0
    rw [eval_ordinaryMinusOneNumerator]
    simp
  have hpositive : 0 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
    (Polynomial.rootMultiplicity_pos hN).mpr hroot
  have hnotTwo : ¬1 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) := by
    intro htwo
    have hderivativeRoot :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mp htwo |>.2
    have hderivative := eval_derivative_ordinaryMinusOneNumerator W 0
    rw [show (ordinaryMinusOneNumerator W).derivative.eval 0 = 0 from
      hderivativeRoot] at hderivative
    simp only [zero_add] at hderivative
    exact ordinaryTailValue_zero_ne_zero W hderivative.symm
  omega

lemma ordinaryNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F)
    (hvalue : frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) = x) :
    (X - C x) ^ 2 ∣ ordinaryMinusOneNumerator W := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot x := by
    change (ordinaryMinusOneNumerator W).eval x = 0
    rw [eval_ordinaryMinusOneNumerator, hvalue]
    simpa only [pow_two] using CharTwo.add_self_eq_zero (x * x)
  have hderivativeRoot : (ordinaryMinusOneNumerator W).derivative.IsRoot x := by
    change (ordinaryMinusOneNumerator W).derivative.eval x = 0
    rw [eval_derivative_ordinaryMinusOneNumerator, hvalue]
    exact CharTwo.add_self_eq_zero x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
