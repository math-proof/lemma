import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil

open AlgebraicCurve Polynomial
open AlgebraicCurve.Place

/--
[AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one.lean)
-/

private lemma _root_.AlgebraicCurve.Place.c3a_adicValuation_le_exp_neg_iff
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F)
  (f : F) (n : ℤ) :
  v.adicValuation f ≤ WithZero.exp (-n) ↔ f = 0 ∨ n ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  ·
    have hne := v.adicValuation_ne_zero hf
    rw [← WithZero.log_le_iff_le_exp hne]
    simp only [hf, false_or, ord]
    omega
p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_le_exp_neg_iff"

private lemma _root_.AlgebraicCurve.Place.c3a_adicValuation_algebraMap_le_one
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F)
  (c : K) : v.adicValuation (algebraMap K F c) ≤ 1 := by
  have h : algebraMap K F c = ((⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) : F) := rfl
  rw [h, v.adicValuation_coe]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_algebraMap_le_one"
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {s : Finset ι}
  {c : ι → K}
  {f : ι → F}
-- given
  (hf : ∀ i ∈ s, f i = 0 ∨ 1 ≤ v.ord (f i))
  (h : v.ord (∑ i ∈ s, algebraMap K F (c i) * f i) = 1) :
-- imply
  ∃ i ∈ s, v.ord (f i) = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hterm : ∀ i ∈ s,
      v.adicValuation (algebraMap K F (c i) * f i) ≤ WithZero.exp (-(2 : ℤ)) := by
-- proof
    intro i hi
    rcases hf i hi with h0 | h1
    · simp [h0]
    ·
      have h2 : (2 : ℤ) ≤ v.ord (f i) := by
        have := hcon i hi
        omega
      rw [map_mul]
      calc v.adicValuation (algebraMap K F (c i)) * v.adicValuation (f i) ≤ 1 * WithZero.exp (-(2 : ℤ)) :=
            mul_le_mul' (v.c3a_adicValuation_algebraMap_le_one (c i))
              ((v.c3a_adicValuation_le_exp_neg_iff (f i) 2).mpr (Or.inr h2))
        _ = WithZero.exp (-(2 : ℤ)) := one_mul _
  have hsum := (v.c3a_adicValuation_le_exp_neg_iff _ 2).mp (v.adicValuation.map_sum_le hterm)
  rcases hsum with h0 | h2
  ·
    rw [h0, AlgebraicCurve.Place.ord_zero] at h
    exact zero_ne_one h
  · omega


-- created on 2026-10-23
