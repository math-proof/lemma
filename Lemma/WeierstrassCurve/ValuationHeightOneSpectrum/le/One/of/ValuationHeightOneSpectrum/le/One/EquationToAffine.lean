import Mathlib
import Initialize.Tactic.Attr.Basic
open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum


/-- ported from external source -/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve K} [W.IsIntegral R]
  {x y : K}
-- given
  (h : W.toAffine.Equation x y)
  (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
-- imply
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1 := by
-- proof
  by_contra hy
  rw [not_le] at hy
  rw [Affine.equation_iff] at h
  have ha₁ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.a₁ ≤ 1 := by
    rw [← integralModel_a₁_eq R W]; apply valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _
  have ha₂ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.a₂ ≤ 1 := by
    rw [← integralModel_a₂_eq R W]; apply valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _
  have ha₃ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.a₃ ≤ 1 := by
    rw [← integralModel_a₃_eq R W]; apply valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _
  have ha₄ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.a₄ ≤ 1 := by
    rw [← integralModel_a₄_eq R W]; apply valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _
  have ha₆ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.a₆ ≤ 1 := by
    rw [← integralModel_a₆_eq R W]; apply valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _
  have hy0 : valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≠ 0 := (zero_lt_one.trans hy).ne'
  have h2 : valuation K (IsDiscreteValuationRing.maximalIdeal R) y < valuation K (IsDiscreteValuationRing.maximalIdeal R) (y ^ 2) := by
    rw [map_pow, pow_two]
    calc
      _ = valuation K (IsDiscreteValuationRing.maximalIdeal R) y * 1 := (mul_one _).symm
      _ < valuation K (IsDiscreteValuationRing.maximalIdeal R) y * valuation K (IsDiscreteValuationRing.maximalIdeal R) y :=
          mul_lt_mul_of_pos_left hy (zero_lt_iff.2 hy0)
  have hxy : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W.a₁ * x * y) ≤ valuation K (IsDiscreteValuationRing.maximalIdeal R) y := by
    rw [map_mul, map_mul]
    calc
      _ ≤ 1 * 1 * valuation K (IsDiscreteValuationRing.maximalIdeal R) y :=
      mul_le_mul' (mul_le_mul' ha₁ hx) le_rfl
      _ = valuation K (IsDiscreteValuationRing.maximalIdeal R) y := by rw [one_mul, one_mul]
  have ha₃y : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W.a₃ * y) ≤ valuation K (IsDiscreteValuationRing.maximalIdeal R) y := by
    rw [map_mul]
    calc
      _ ≤ 1 * valuation K (IsDiscreteValuationRing.maximalIdeal R) y := mul_le_mul' ha₃ le_rfl
      _ = valuation K (IsDiscreteValuationRing.maximalIdeal R) y := one_mul _
  have e1 : valuation K (IsDiscreteValuationRing.maximalIdeal R) (y ^ 2 + W.a₁ * x * y) = valuation K (IsDiscreteValuationRing.maximalIdeal R) (y ^ 2) :=
    Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hxy h2)
  have e2 : valuation K (IsDiscreteValuationRing.maximalIdeal R) (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = valuation K (IsDiscreteValuationRing.maximalIdeal R) (y ^ 2) := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [e1]; apply lt_of_le_of_lt ha₃y h2), e1]
  have hR : valuation K (IsDiscreteValuationRing.maximalIdeal R) (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 := by
    have hx3 : valuation K (IsDiscreteValuationRing.maximalIdeal R) (x ^ 3) ≤ 1 := by
      rw [map_pow]; apply pow_le_one' hx 3
    have hax2 : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W.a₂ * x ^ 2) ≤ 1 := by
      rw [map_mul, map_pow]; apply mul_le_one' ha₂ (pow_le_one' hx 2)
    refine Valuation.map_add_le _
      (Valuation.map_add_le _ (Valuation.map_add_le _ hx3 hax2) (by rw [map_mul]; apply mul_le_one' ha₄ hx)) ha₆
  rw [h] at e2
  exact absurd (hy.trans (h2.trans_le (e2 ▸ hR))) (lt_irrefl 1)


-- created on 2026-10-24
