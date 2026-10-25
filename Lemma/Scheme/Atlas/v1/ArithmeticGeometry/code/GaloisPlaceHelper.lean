import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
open IsDedekindDomain WithZero


/--
[aux_false_of_forall_le_neg_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisPlaceHelper.lean)
-/
@[path]
private lemma aux_false_of_forall_le_neg_nat_eq
  {b' : Multiplicative ℤ}
-- given
  (h : ∀ n : ℕ, b'.toAdd ≤ -(n : ℤ)) :
-- imply
  False := by
-- proof
  apply aux_false_of_forall_le_neg_nat b' h

/--
[aux_eq_of_iff_le_neg_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisPlaceHelper.lean)
-/
@[path]
private lemma aux_eq_of_iff_le_neg_nat_eq
  {x y : ℤ}
-- given
  (hx : x ≤ 0)
  (hy : y ≤ 0)
  (h : ∀ n : ℕ, x ≤ -(n : ℤ) ↔ y ≤ -(n : ℤ)) :
-- imply
  x = y := by
-- proof
  apply aux_eq_of_iff_le_neg_nat x y hx hy h

/--
[WithZero.eq_of_le_exp_neg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisPlaceHelper.lean)
-/
@[path]
private lemma eq_of_le_exp_neg_iff_eq
  {a b : ℤᵐ⁰}
-- given
  (ha : a ≤ 1)
  (hb : b ≤ 1)
  (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ)) ↔ b ≤ exp (-(n : ℤ))) :
-- imply
  a = b := by
-- proof
  apply WithZero.eq_of_le_exp_neg_iff ha hb h

/--
[mem_equivOfRingEquiv_pow_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisPlaceHelper.lean)
-/
@[path]
private lemma mem_equivOfRingEquiv_pow_iff_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {e : R ≃+* R}
  {v : HeightOneSpectrum R}
  {r : R}
  {n : ℕ} :
-- imply
  r ∈ (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal ^ n ↔ e.symm r ∈ v.asIdeal ^ n := by
-- proof
  apply mem_equivOfRingEquiv_pow_iff e v r n

/--
[intValuation_equivOfRingEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GaloisPlaceHelper.lean)
-/
@[path]
private lemma intValuation_equivOfRingEquiv_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {e : R ≃+* R}
  {v : HeightOneSpectrum R}
  {r : R} :
-- imply
  v.intValuation (e.symm r) = (HeightOneSpectrum.equivOfRingEquiv e v).intValuation r := by
-- proof
  apply intValuation_equivOfRingEquiv e v r


-- created on 2026-10-23
