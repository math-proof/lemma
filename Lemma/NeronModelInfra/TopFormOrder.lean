import Mathlib
import Def.NeronModelInfra_TopFormOrder

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct

namespace NeronModelInfra.TopFormOrder

variable (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
  [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
  [IsScalarTower R' O F] [IsScalarTower R' K' F] (d : ℕ)


section Order

variable [IsDomain O] [IsDiscreteValuationRing O]
variable (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] [Algebra K' L] [Algebra R' L]
  [IsScalarTower R' O L] [IsScalarTower R' K' L]


omit K' d in

theorem addOrd_uniformizer (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) :
    addOrd O L (algebraMap O L ϖ) = 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; apply IsDiscreteValuationRing.not_a_field O; simpa [h] using hϖ
  have hne : algebraMap O L ϖ ≠ 0 := by
    simpa using (IsFractionRing.injective O L).ne hϖ0
  unfold addOrd
  rw [dif_neg hne]
  have hv : (maximalSpectrum O).valuation L (algebraMap O L ϖ) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (maximalSpectrum O).intValuation_singleton hϖ0 hϖ
  have : WithZero.unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr hne) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
  rw [this]; simp

omit K' d in

theorem addOrd_uniformizer_sq (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) :
    addOrd O L (algebraMap O L ϖ ^ 2) = 2 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; apply IsDiscreteValuationRing.not_a_field O; simpa [h] using hϖ
  have hne : algebraMap O L ϖ ≠ 0 := by
    simpa using (IsFractionRing.injective O L).ne hϖ0
  have hne2 : algebraMap O L ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hne
  unfold addOrd
  rw [dif_neg hne2]
  have hv : (maximalSpectrum O).valuation L (algebraMap O L ϖ ^ 2) = Multiplicative.ofAdd (-2 : ℤ) := by
    rw [map_pow, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      (maximalSpectrum O).intValuation_singleton hϖ0 hϖ]; rfl
  have : WithZero.unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr hne2) =
      Multiplicative.ofAdd (-2 : ℤ) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
  rw [this]; simp

end Order

end NeronModelInfra.TopFormOrder

end
