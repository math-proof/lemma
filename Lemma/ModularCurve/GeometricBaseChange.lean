import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Module.LinearMap.Rat
import Lemma.ModularCurve.LaurentCoeff
import Instance.FieldTheory_RatAlgClosureGalois
import Instance.ModularCurve_GeometricBaseChange

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open IntermediateField

namespace ModularCurve

section LinearDisjoint

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem linearIndependent_coeffEmb {ι : Type*} {v : ι → LaurentSeries ℚ}
    (hv : LinearIndependent ℚ v) : LinearIndependent L (fun i => coeffEmb L (v i)) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  let b := Module.Free.chooseBasis ℚ L
  refine b.forall_coord_eq_zero_iff.mp fun k => ?_
  have hk : ∑ j ∈ s, (b.coord k (g j)) • v j = 0 := by
    ext n
    have hn := congrArg (fun x : LaurentSeries L => b.coord k (x.coeff n)) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul,
      HahnSeries.coeff_zero, map_zero] at hn
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  exact hv s (fun j => b.coord k (g j)) hk i hi

end LinearDisjoint

section BaseChange

variable (L : Type*) [Field L]

private theorem algebraMap_mul_eq_smul (c : L) (y : LaurentSeries L) :
    algebraMap L (LaurentSeries L) c * y = c • y := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]

variable [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def baseChangeRatAlgHom : L ⊗[ℚ] F₀ →ₐ[ℚ] LaurentSeries L :=
  Algebra.TensorProduct.productMap (algebraMap L (LaurentSeries L)).toRatAlgHom
    ((coeffEmb L).comp (F₀.val : F₀ →+* LaurentSeries ℚ)).toRatAlgHom

theorem baseChangeRatAlgHom_tmul (c : L) (f : F₀) :
    baseChangeRatAlgHom L F₀ (c ⊗ₜ f) =
      algebraMap L (LaurentSeries L) c * coeffEmb L (f : LaurentSeries ℚ) :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ c f

def baseChangeHom : L ⊗[ℚ] F₀ →ₐ[L] LaurentSeries L :=
  { baseChangeRatAlgHom L F₀ with
    commutes' := fun c => by
      change baseChangeRatAlgHom L F₀ (algebraMap L (L ⊗[ℚ] F₀) c) =
        algebraMap L (LaurentSeries L) c
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        baseChangeRatAlgHom_tmul, OneMemClass.coe_one, map_one, mul_one] }

@[simp]
theorem baseChangeHom_tmul (c : L) (f : F₀) :
    baseChangeHom L F₀ (c ⊗ₜ f) =
      algebraMap L (LaurentSeries L) c * coeffEmb L (f : LaurentSeries ℚ) :=
  baseChangeRatAlgHom_tmul L F₀ c f

theorem baseChangeHom_one_tmul (f : F₀) :
    baseChangeHom L F₀ (1 ⊗ₜ f) = coeffEmb L (f : LaurentSeries ℚ) := by
  rw [baseChangeHom_tmul, map_one, one_mul]

private def baseChangeLinear : L ⊗[ℚ] F₀ →ₗ[L] LaurentSeries L where
  toFun := baseChangeHom L F₀
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, ← algebraMap_mul_eq_smul, ← (baseChangeHom L F₀).commutes c,
      ← map_mul, ← Algebra.smul_def]

private theorem baseChangeLinear_apply (x : L ⊗[ℚ] F₀) :
    baseChangeLinear L F₀ x = baseChangeHom L F₀ x := rfl

private def valRatLinear : F₀ →ₗ[ℚ] LaurentSeries ℚ :=
  ((F₀.val : F₀ →+* LaurentSeries ℚ) : F₀ →+ LaurentSeries ℚ).toRatLinearMap

private theorem valRatLinear_apply (f : F₀) : valRatLinear F₀ f = (f : LaurentSeries ℚ) := rfl

private theorem baseChangeLinear_injective : Function.Injective (baseChangeLinear L F₀) := by
  classical
  let bF := Module.Free.chooseBasis ℚ F₀
  let B := Algebra.TensorProduct.basis L bF
  have hli : LinearIndependent L (baseChangeLinear L F₀ ∘ B) := by
    have h : (baseChangeLinear L F₀ ∘ B : _ → LaurentSeries L) =
        fun i => coeffEmb L (valRatLinear F₀ (bF i)) := by
      funext i
      rw [Function.comp_apply, baseChangeLinear_apply, Algebra.TensorProduct.basis_apply,
        baseChangeHom_one_tmul, valRatLinear_apply]
    rw [h]
    refine linearIndependent_coeffEmb L ?_
    refine bF.linearIndependent.map' (valRatLinear F₀) (LinearMap.ker_eq_bot.mpr ?_)
    exact Subtype.val_injective
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hrepr : Finsupp.linearCombination L (baseChangeLinear L F₀ ∘ B) (B.repr x) = 0 := by
    rw [← Finsupp.apply_linearCombination, B.linearCombination_repr]
    exact hx
  have h0 : B.repr x = 0 := linearIndependent_iff.mp hli (B.repr x) hrepr
  rw [← B.linearCombination_repr x, h0, map_zero]

theorem baseChangeHom_injective : Function.Injective (baseChangeHom L F₀) :=
  baseChangeLinear_injective L F₀

theorem baseChangeHom_mem (x : L ⊗[ℚ] F₀) :
    baseChangeHom L F₀ x ∈ laurentBaseChange L F₀ := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c f =>
      rw [baseChangeHom_tmul]
      exact mul_mem ((laurentBaseChange L F₀).algebraMap_mem c)
        (coeffEmb_mem_laurentBaseChange L f.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

variable [Algebra.IsAlgebraic ℚ L]

theorem isField_tensorProduct : IsField (L ⊗[ℚ] F₀) :=
  Algebra.TensorProduct.isField_of_isAlgebraic ℚ L F₀ (Or.inl inferInstance)

private theorem isField_range_baseChangeHom : IsField (baseChangeHom L F₀).range :=
  MulEquiv.isField (isField_tensorProduct L F₀)
    (AlgEquiv.ofInjective _ (baseChangeHom_injective L F₀)).symm.toMulEquiv

theorem exists_baseChangeHom_eq {y : LaurentSeries L} (hy : y ∈ laurentBaseChange L F₀) :
    ∃ x : L ⊗[ℚ] F₀, baseChangeHom L F₀ x = y := by
  let K : IntermediateField L (LaurentSeries L) :=
    (baseChangeHom L F₀).range.toIntermediateField' (isField_range_baseChangeHom L F₀)
  have hle : laurentBaseChange L F₀ ≤ K := by
    change IntermediateField.adjoin L _ ≤ K
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨(1 : L) ⊗ₜ ⟨f, hf⟩, baseChangeHom_one_tmul L F₀ ⟨f, hf⟩⟩
  exact hle hy

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

@[simp]
theorem coe_baseChangeEquiv_apply (x : L ⊗[ℚ] F₀) :
    (baseChangeEquiv L F₀ x : LaurentSeries L) = baseChangeHom L F₀ x := rfl

theorem baseChangeEquiv_one_tmul (f : F₀) :
    baseChangeEquiv L F₀ (1 ⊗ₜ f) = ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ :=
  Subtype.ext (baseChangeHom_one_tmul L F₀ f)

theorem baseChangeEquiv_symm_coeffEmb (f : F₀) :
    (baseChangeEquiv L F₀).symm ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ = 1 ⊗ₜ f := by
  rw [← baseChangeEquiv_one_tmul, AlgEquiv.symm_apply_apply]

theorem baseChangeEquiv_tmul (c : L) (f : F₀) :
    baseChangeEquiv L F₀ (c ⊗ₜ f) =
      algebraMap L (laurentBaseChange L F₀) c *
        ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ := by
  rw [show c ⊗ₜ[ℚ] f = algebraMap L (L ⊗[ℚ] F₀) c * (1 ⊗ₜ f) by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
    map_mul, AlgEquiv.commutes, baseChangeEquiv_one_tmul]

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

theorem geomAut_apply (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) :
    geomAut L F₀ σ x = baseChangeEquiv L F₀
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) σ ((baseChangeEquiv L F₀).symm x)) :=
  rfl

theorem geomAut_baseChangeEquiv_tmul (σ : F₀ ≃ₐ[ℚ] F₀) (c : L) (f : F₀) :
    geomAut L F₀ σ (baseChangeEquiv L F₀ (c ⊗ₜ f)) = baseChangeEquiv L F₀ (c ⊗ₜ σ f) := by
  rw [geomAut_apply, AlgEquiv.symm_apply_apply]
  rfl

theorem geomAut_coeffEmb (σ : F₀ ≃ₐ[ℚ] F₀) (f : F₀) :
    geomAut L F₀ σ ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ =
      ⟨coeffEmb L (σ f), coeffEmb_mem_laurentBaseChange L (σ f).2⟩ := by
  rw [← baseChangeEquiv_one_tmul, geomAut_baseChangeEquiv_tmul, baseChangeEquiv_one_tmul]

theorem coe_geomAut_coeffEmb (σ : F₀ ≃ₐ[ℚ] F₀) (f : F₀) :
    (geomAut L F₀ σ ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ : LaurentSeries L) =
      coeffEmb L (σ f) :=
  congrArg Subtype.val (geomAut_coeffEmb L F₀ σ f)

end BaseChange

end ModularCurve

end
