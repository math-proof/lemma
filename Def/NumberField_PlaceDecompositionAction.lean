module

public import Mathlib
public import Abbrev.NumberField_PlaceDecompositionAction

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp


variable {E K : Type*} [Field E] [Field K] [NumberField K] [Algebra E K] {w : HeightOneSpectrum (𝓞 K)}

noncomputable def actRingEquiv (σ : decomp E K w) : w.adicCompletion K ≃+* w.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithVal.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E] K) (σ⁻¹).2).continuous))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w).symm

noncomputable def actHom : decomp E K w →* (w.adicCompletion K ≃+* w.adicCompletion K) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

noncomputable scoped instance instSMulWithVal : SMul (decomp E K w) (WithVal (w.valuation K)) where
  smul σ y := WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) y.ofVal)

noncomputable scoped instance instMulActionWithVal : MulAction (decomp E K w) (WithVal (w.valuation K)) where
  one_smul y := by
    change WithVal.toVal _ (((1 : decomp E K w) : K ≃ₐ[E] K) y.ofVal) = y
    rw [Subgroup.coe_one, AlgEquiv.one_apply, WithVal.toVal_ofVal]
  mul_smul σ τ y := by
    change WithVal.toVal _ (((σ * τ : decomp E K w) : K ≃ₐ[E] K) y.ofVal) =
      WithVal.toVal _ ((σ : K ≃ₐ[E] K)
        (WithVal.ofVal (WithVal.toVal _ (((τ : decomp E K w) : K ≃ₐ[E] K) y.ofVal))))
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, WithVal.ofVal_toVal]

noncomputable scoped instance instDistribMulActionWithVal : DistribMulAction (decomp E K w) (WithVal (w.valuation K)) where
  smul_zero σ := by
    change WithVal.toVal _ ((σ : K ≃ₐ[E] K) (0 : WithVal (w.valuation K)).ofVal) = 0
    rw [WithVal.ofVal_zero, map_zero, WithVal.toVal_zero]
  smul_add σ x y := by
    change WithVal.toVal _ ((σ : K ≃ₐ[E] K) (x + y).ofVal) =
      WithVal.toVal _ ((σ : K ≃ₐ[E] K) x.ofVal) + WithVal.toVal _ ((σ : K ≃ₐ[E] K) y.ofVal)
    rw [WithVal.ofVal_add, map_add, WithVal.toVal_add]

noncomputable scoped instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul (decomp E K w) (WithVal (w.valuation K)) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) (w.adicCompletion K) where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight


end NumberField.PlaceDecomp

end
