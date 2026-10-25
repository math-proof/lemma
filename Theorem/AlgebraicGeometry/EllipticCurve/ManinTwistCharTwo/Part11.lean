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
import Def.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part12
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

lemma count_roots_ordinaryMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (x : F) :
    Multiset.count x (ordinaryMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hx : x = 0
  · subst x
    have hlinearN : X - C 0 ∣ ordinaryMinusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (ordinaryMinusOneNumerator W).eval 0 = 0
      rw [eval_ordinaryMinusOneNumerator]
      simp
    have hlinearL' : X - C 0 ∣
        (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
      hlinearL.trans ⟨charTwoFrobeniusPolynomial, by ring⟩
    have hcommon : X - C 0 ∣ ordinaryMinusOneGCD W := by
      unfold ordinaryMinusOneGCD
      exact dvd_gcd hlinearN hlinearL'
    have hlower : 1 ≤
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper :
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤
            Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN 0
        _ = 1 := rootMultiplicity_ordinaryNumerator_zero W
    have hroot : Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot, charTwoFiber_card_eq_one]
  · rcases frobeniusValue_eq_zero_or_eq
        (c := (ordinaryH W).eval x) hx with hvalue | hvalue
    · have hupper :
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
          _ = 0 := rootMultiplicity_ordinaryNumerator_eq_zero W x hx hvalue
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_two_of_value_eq_zero hx hvalue]
    · have hcommon : (X - C x) ^ 2 ∣ ordinaryMinusOneGCD W := by
        unfold ordinaryMinusOneGCD
        exact dvd_gcd (ordinaryNumerator_sq_dvd_of_value_eq W x hvalue)
          hlinearLsq
      have hlower : 2 ≤
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL : Polynomial.rootMultiplicity x
          ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_charTwoFrobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 2 :=
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x
                ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_zero_of_value_eq hx hvalue]

lemma ordinaryMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (ordinaryMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots) =
        (ordinaryMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (ordinaryMinusOneGCD W).roots) (by simp))
  calc
    (ordinaryMinusOneGCD W).natDegree =
        (ordinaryMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_ordinaryMinusOneGCD W x

lemma ordinaryMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x)) =
      2 * Nat.card F := by
  rw [ordinaryMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) +
        Nat.card (charTwoFiber x ((ordinaryH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two x _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

lemma ordinaryMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : ordinaryMinusOneGCD W *
      (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W) =
        ordinaryMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, ordinaryMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := ordinaryMinusOneGCD_natDegree_add_fiber_sum W
  omega

lemma num_natDegree_ordinaryMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact ordinaryMinusOneQuotient_natDegree W

lemma ordinaryPaperX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) =
      algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [ordinaryPaperX_addX_Q_eq W ordinaryPZeroX_ne_QX]
  rw [ordinaryPaperX_pZeroX, ordinaryPaperY_neg_pZeroY W]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [ordinaryMinusOneNumerator, map_add, map_pow,
    RatFunc.algebraMap_X, sub_eq_add_neg, CharTwo.neg_eq]
  let q := Nat.card F
  let t : RatFunc F := RatFunc.X
  let r := t ^ q
  let u := algebraMap F[X] (RatFunc F) (ordinaryU W)
  let a := RatFunc.C W.a₂
  let b := RatFunc.C W.a₆
  let s := u / t + r
  let L := r + t
  let n := t ^ (2 * q + 1) + t ^ (q + 2) + t ^ (q + 1) + u
  change (s / L) ^ 2 + s / L + b / t ^ 2 + r = n / L ^ 2
  have ht : t ≠ 0 := RatFunc.X_ne_zero
  have hL : L ≠ 0 := by
    dsimp only [L, r, t, q]
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hu := congrArg (algebraMap F[X] (RatFunc F)) (ordinaryU_identity W)
  rw [ordinaryH_pow_card W] at hu
  simp only [ordinaryH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hu
  change u ^ 2 + t ^ (q + 1) * u =
    t ^ 2 * (t ^ (3 * q) + a * t ^ (2 * q) + b) +
      t ^ (2 * q) * (t ^ 3 + a * t ^ 2 + b) at hu
  have htq1 : t ^ (q + 1) = t * r := by
    dsimp only [r]
    rw [pow_succ]
    ring
  have ht2q : t ^ (2 * q) = r ^ 2 := by
    dsimp only [r]
    calc
      t ^ (2 * q) = t ^ (q * 2) := by congr 1; omega
      _ = (t ^ q) ^ 2 := pow_mul t q 2
  have ht3q : t ^ (3 * q) = r ^ 3 := by
    dsimp only [r]
    calc
      t ^ (3 * q) = t ^ (q * 3) := by congr 1; omega
      _ = (t ^ q) ^ 3 := pow_mul t q 3
  rw [htq1, ht2q, ht3q] at hu
  have hu' : u ^ 2 + t * r * u =
      t ^ 2 * r ^ 3 + b * t ^ 2 + t ^ 3 * r ^ 2 + b * r ^ 2 := by
    have hcancel : a * t ^ 2 * r ^ 2 + a * t ^ 2 * r ^ 2 = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination hu + hcancel
  dsimp only [s, n]
  field_simp [ht, hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hu' +
    (u * t * t ^ q + t * t ^ q * b + t ^ 2 * t ^ (q * 2) +
      t ^ 2 * t ^ (q * 3) + t ^ 2 * b + t ^ 3 * t ^ (q * 2) +
        t ^ (q * 2) * b) * htwo

lemma ordinaryPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∃ y hxy, ordinaryPoint W (-1) =
      .some
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) y hxy := by
  have hp : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryPZero_equation W)
  have hneg : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F))
      ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
        (ordinaryPZeroY W)) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -ordinaryPZero W = .some (ordinaryPZeroX (F := F))
        ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
          (ordinaryPZeroY W)) hneg := by
    rw [show ordinaryPZero W =
      .some (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) ordinaryPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryQ_equation W))
  rw [← hnegP, ← show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
    at hadd
  have hpoint : ordinaryPoint W (-1) =
      -(-ordinaryPZero W + ordinaryQ W) := by
    unfold ordinaryPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

lemma ordinaryD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := ordinaryPoint_neg_one_eq_some W
  unfold ordinaryD
  rw [hpoint]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)))).natDegree = _
  rw [ordinaryPaperX_negPZero_add_Q W]
  rw [num_natDegree_ordinaryMinusOneRat W]
  exact (ordinaryPointCount_eq_fiber_sum W).symm

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
