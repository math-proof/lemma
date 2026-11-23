module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Theorem.LaurentSeries.LaurentCoeff
public import Instance.FieldTheory_RatAlgClosureGalois

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open IntermediateField

namespace ModularCurve


section BaseChange

variable (L : Type*) [Field L]

variable [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def baseChangeRatAlgHom : L ⊗[ℚ] F₀ →ₐ[ℚ] LaurentSeries L :=
  Algebra.TensorProduct.productMap (algebraMap L (LaurentSeries L)).toRatAlgHom
    ((coeffEmb L).comp (F₀.val : F₀ →+* LaurentSeries ℚ)).toRatAlgHom

def baseChangeHom : L ⊗[ℚ] F₀ →ₐ[L] LaurentSeries L :=
  { baseChangeRatAlgHom L F₀ with
    commutes' := fun c => by
      change baseChangeRatAlgHom L F₀ (algebraMap L (L ⊗[ℚ] F₀) c) =
        algebraMap L (LaurentSeries L) c
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        baseChangeRatAlgHom_tmul, OneMemClass.coe_one, map_one, mul_one] }

private def baseChangeLinear : L ⊗[ℚ] F₀ →ₗ[L] LaurentSeries L where
  toFun := baseChangeHom L F₀
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, ← algebraMap_mul_eq_smul, ← (baseChangeHom L F₀).commutes c,
      ← map_mul, ← Algebra.smul_def]

private def valRatLinear : F₀ →ₗ[ℚ] LaurentSeries ℚ :=
  ((F₀.val : F₀ →+* LaurentSeries ℚ) : F₀ →+ LaurentSeries ℚ).toRatLinearMap

variable [Algebra.IsAlgebraic ℚ L]

def baseChangeEquiv : L ⊗[ℚ] F₀ ≃ₐ[L] laurentBaseChange L F₀ :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨baseChangeHom L F₀ x, baseChangeHom_mem L F₀ x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun c => Subtype.ext ((baseChangeHom L F₀).commutes c) }
    ⟨fun x y h => baseChangeHom_injective L F₀ (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := exists_baseChangeHom_eq L F₀ y.2
      exact ⟨x, Subtype.ext hx⟩⟩

def geomAut : (F₀ ≃ₐ[ℚ] F₀) →* (laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀) :=
  MonoidHom.mk'
    (fun σ => ((baseChangeEquiv L F₀).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) σ)).trans (baseChangeEquiv L F₀))
    (fun σ τ => AlgEquiv.ext fun x => by
      change baseChangeEquiv L F₀ (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (σ * τ)
          ((baseChangeEquiv L F₀).symm x)) =
        baseChangeEquiv L F₀ (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) σ
          ((baseChangeEquiv L F₀).symm (baseChangeEquiv L F₀
            (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) τ
              ((baseChangeEquiv L F₀).symm x)))))
      rw [AlgEquiv.symm_apply_apply]
      congr 1
      induction (baseChangeEquiv L F₀).symm x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c f => rfl
      | add y z hy hz => simp only [map_add, hy, hz])

end BaseChange

end ModularCurve

end

end
