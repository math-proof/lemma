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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part12
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

lemma count_roots_minusOneGCD [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) :
    Multiset.count x (minusOneGCD W).roots =
      2 - Nat.card (squareFiber W x) := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (frobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_frobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣ (frobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hzero : (cubic W).eval x = 0
  · have hlinearB : X - C x ∣ minusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (minusOneNumerator W).eval x = 0
      rw [eval_minusOneNumerator, hzero]
      ring
    have hlinearL' : X - C x ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
      exact hlinearL.trans ⟨frobeniusPolynomial, by ring⟩
    have hcommon : X - C x ∣ minusOneGCD W := by
      unfold minusOneGCD
      exact dvd_gcd hlinearB hlinearL'
    have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity x (minusOneGCD W) ≤
            Polynomial.rootMultiplicity x (minusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
        _ = 1 := rootMultiplicity_minusOneNumerator_eq_one
          hchar W hcard x hzero
    have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      squareFiber_natCard_eq_one W x hzero]
  · by_cases hsquare : IsSquare ((cubic W).eval x)
    · have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x (minusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
          _ = 0 := rootMultiplicity_minusOneNumerator_eq_zero
            hchar W x hzero hsquare
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_two hchar W x hzero hsquare]
    · have hcommon : (X - C x) ^ 2 ∣ minusOneGCD W := by
        unfold minusOneGCD
        exact dvd_gcd
          (sq_X_sub_C_dvd_minusOneNumerator hchar W x hsquare) hlinearLsq
      have hlower : 2 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL :
          Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_frobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 2 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_zero W x hsquare]

lemma minusOneGCD_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (minusOneGCD W).Splits :=
    (frobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (minusOneGCD W).roots) =
        (minusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (minusOneGCD W).roots) (by simp))
  calc
    (minusOneGCD W).natDegree = (minusOneGCD W).roots.card :=
      hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (minusOneGCD W).roots := hsum.symm
    _ = ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_minusOneGCD hchar W hcard x

lemma minusOneGCD_natDegree_add_fiber_sum [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree + ∑ x : F, Nat.card (squareFiber W x) =
      2 * Nat.card F := by
  rw [minusOneGCD_natDegree hchar W hcard]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (squareFiber W x) +
        Nat.card (squareFiber W x))) = ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (squareFiber_natCard_le_two hchar W x)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

lemma equation_iff_square (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 = (cubic W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharNeTwoNF,
    WeierstrassCurve.a₃_of_isCharNeTwoNF, zero_mul]
  simp only [cubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  simp

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
