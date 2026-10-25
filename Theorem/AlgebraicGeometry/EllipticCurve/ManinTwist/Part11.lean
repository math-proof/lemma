/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
import Lemma.Int.EllipticCurve.ManinSequence
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
import Lemma.Scheme.EllipticCurve.VariableChangePoint
import Lemma.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Def.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Instance.AlgebraicGeometry.EllipticCurve.ManinTwist.Part4
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

lemma eval_eulerPolynomial [Fintype F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) (x : F) :
    (eulerPolynomial W).eval x =
      ((quadraticChar F) ((cubic W).eval x) : F) := by
  have hhalf :
      Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  have hcriterion :=
    quadraticChar_eq_pow_of_char_ne_two' hchar ((cubic W).eval x)
  rw [hhalf] at hcriterion
  unfold eulerPolynomial
  rw [eval_pow, Nat.card_eq_fintype_card]
  exact hcriterion.symm

lemma eval_eulerPolynomial_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (eulerPolynomial W).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar, hzero]
  simp

lemma eval_eulerPolynomial_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [(quadraticChar_one_iff_isSquare hzero).mpr hsquare]
  simp

lemma eval_eulerPolynomial_eq_neg_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = -1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsquare]
  simp

lemma eval_derivative_minusOneNumerator_of_cubic_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (minusOneNumerator W).derivative.eval x = (cubic W).derivative.eval x := by
  have heuler := eval_eulerPolynomial_eq_zero hchar W x hzero
  have hfrobenius := eval_frobeniusPolynomial (F := F) x
  unfold minusOneNumerator
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_add,
    derivative_one, eval_sub, eval_add, eval_mul, eval_pow, eval_one]
  rw [hzero, heuler, hfrobenius]
  ring

lemma eval_derivative_cubic_ne_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (x : F) (hzero : (cubic W).eval x = 0) :
    (cubic W).derivative.eval x ≠ 0 := by
  intro hderivative
  obtain ⟨u, v, huv⟩ :=
    (Polynomial.separable_def (cubic W)).mp (cubic_separable W)
  have heval := congrArg (Polynomial.eval x) huv
  simp only [eval_add, eval_mul, eval_one] at heval
  rw [hzero, hderivative] at heval
  simp at heval

lemma minusOneNumerator_ne_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) : minusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := minusOneNumerator_natDegree hchar W hcard
  rw [hzero] at hdegree
  simp at hdegree

lemma rootMultiplicity_minusOneNumerator_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) (hzero : (cubic W).eval x = 0) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hroot : (minusOneNumerator W).IsRoot x := by
    change (minusOneNumerator W).eval x = 0
    rw [eval_minusOneNumerator, hzero]
    ring
  have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneNumerator W) := by
    rw [Polynomial.le_rootMultiplicity_iff hB]
    simpa using (Polynomial.dvd_iff_isRoot.mpr hroot)
  have hupper : Polynomial.rootMultiplicity x (minusOneNumerator W) ≤ 1 := by
    rw [Polynomial.rootMultiplicity_le_iff hB]
    intro hsquare
    have hderivative := eval_derivative_eq_zero_of_sq_dvd hsquare
    rw [eval_derivative_minusOneNumerator_of_cubic_eq_zero hchar W x hzero]
      at hderivative
    exact eval_derivative_cubic_ne_zero W x hzero hderivative
  omega

lemma rootMultiplicity_minusOneNumerator_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heuler := eval_eulerPolynomial_eq_one hchar W x hzero hsquare
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hsum : (1 + 1 : F) ≠ 0 := by
    intro h
    apply htwo
    norm_num at h ⊢
    exact h
  have heval : (minusOneNumerator W).eval x ≠ 0 := by
    rw [eval_minusOneNumerator, heuler]
    exact mul_ne_zero hzero (pow_ne_zero 2 hsum)
  exact heval hroot

lemma sq_X_sub_C_dvd_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (X - C x) ^ 2 ∣ minusOneNumerator W := by
  have heuler := eval_eulerPolynomial_eq_neg_one hchar W x hsquare
  have heulerRoot : (eulerPolynomial W + 1).IsRoot x := by
    simp only [IsRoot, eval_add, eval_one, heuler]
    ring
  have hfrobeniusRoot : (frobeniusPolynomial : F[X]).IsRoot x :=
    eval_frobeniusPolynomial x
  obtain ⟨u, hu⟩ := Polynomial.dvd_iff_isRoot.mpr heulerRoot
  obtain ⟨v, hv⟩ := Polynomial.dvd_iff_isRoot.mpr hfrobeniusRoot
  refine ⟨cubic W * u ^ 2 - (C W.a₂ + X ^ Nat.card F + X) * v ^ 2, ?_⟩
  unfold minusOneNumerator
  rw [hu, hv]
  ring

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
