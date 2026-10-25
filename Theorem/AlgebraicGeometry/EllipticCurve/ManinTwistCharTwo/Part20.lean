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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part20
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

lemma count_roots_superMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F) :
    Multiset.count x (superMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) := by
  have hN := superMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  rcases frobeniusValue_eq_zero_or_eq
      (c := (superH W).eval x) ha with hvalue | hvalue
  · have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 0 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
        _ = 0 := rootMultiplicity_superNumerator_eq_zero W x hvalue
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 0 :=
      Nat.eq_zero_of_le_zero hupper
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_two_of_value_eq_zero ha hvalue]
  · have hcommon : (X - C x) ^ 2 ∣ superMinusOneGCD W := by
      unfold superMinusOneGCD
      exact dvd_gcd (superNumerator_sq_dvd_of_value_eq W x hvalue)
        hlinearLsq
    have hlower : 2 ≤ Polynomial.rootMultiplicity x (superMinusOneGCD W) :=
      (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
    have hrootL : Polynomial.rootMultiplicity x
        ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
      rw [← Polynomial.count_roots]
      exact count_roots_charTwoFrobeniusPolynomial_sq x
    have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 2 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x
              ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
        _ = 2 := hrootL
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 2 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_zero_of_value_eq ha hvalue]

lemma superMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (superMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (superMinusOneGCD W).roots) =
        (superMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (superMinusOneGCD W).roots) (by simp))
  calc
    (superMinusOneGCD W).natDegree =
        (superMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (superMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_superMinusOneGCD W x

lemma superMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) =
      2 * Nat.card F := by
  rw [superMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) +
        Nat.card (charTwoFiber W.a₃ ((superH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two W.a₃ _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

lemma superMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneNumerator W / superMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  have hN := superMinusOneNumerator_ne_zero W
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : superMinusOneGCD W *
      (superMinusOneNumerator W / superMinusOneGCD W) =
        superMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : superMinusOneNumerator W / superMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, superMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := superMinusOneGCD_natDegree_add_fiber_sum W
  omega

lemma num_natDegree_superMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact superMinusOneQuotient_natDegree W

lemma superD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := superPoint_neg_one_eq_some W
  unfold superD
  rw [hpoint]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0))).natDegree = _
  rw [superX_negPZero_add_Q W]
  rw [num_natDegree_superMinusOneRat W]
  exact (superPointCount_eq_fiber_sum W).symm

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
