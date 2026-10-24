import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[exists_isAlgClosed_algHom_algHom_of_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_isAlgClosed_algHom_algHom_of_injective.lean)
-/
@[path]
private lemma main
  (D : Type) [CommRing D] [IsDomain D]
  (E₁ E₂ : Type) [Field E₁] [Field E₂] [Algebra D E₁] [Algebra D E₂]
  (h₁ : Function.Injective (algebraMap D E₁)) (h₂ : Function.Injective (algebraMap D E₂)) :
  -- imply
  ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (_ : Algebra D Ω'),
    Nonempty (E₁ →ₐ[D] Ω') ∧ Nonempty (E₂ →ₐ[D] Ω') := by
  -- proof
  classical
  let F := FractionRing D
  let alg₁ : Algebra F E₁ := (IsFractionRing.lift (K := F) h₁).toAlgebra
  let alg₂ : Algebra F E₂ := (IsFractionRing.lift (K := F) h₂).toAlgebra
  let st₁ : IsScalarTower D F E₁ := IsScalarTower.of_algebraMap_eq (fun d => by
    show algebraMap D E₁ d = IsFractionRing.lift h₁ (algebraMap D F d)
    rw [IsFractionRing.lift_algebraMap])
  let st₂ : IsScalarTower D F E₂ := IsScalarTower.of_algebraMap_eq (fun d => by
    show algebraMap D E₂ d = IsFractionRing.lift h₂ (algebraMap D F d)
    rw [IsFractionRing.lift_algebraMap])
  let T := TensorProduct E₁ E₂
  let _ : Nontrivial T := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let Ω₀ := T ⧸ m
  let _ : Field Ω₀ := Ideal.Quotient.field m
  let Ω' := AlgebraicClosure Ω₀
  let algT : Algebra D T := ((algebraMap F T).comp (algebraMap D F)).toAlgebra
  let toΩ : T →+* Ω' := (algebraMap Ω₀ Ω').comp (Ideal.Quotient.mk m)
  let algΩ : Algebra D Ω' := (toΩ.comp (algebraMap D T)).toAlgebra
  refine ⟨Ω', inferInstance, inferInstance, algΩ, ⟨?_⟩, ⟨?_⟩⟩
  ·
    refine { toRingHom := toΩ.comp (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := E₁) (B := E₂)).toRingHom,
      commutes' := fun d => ?_ }
    show toΩ (Algebra.TensorProduct.includeLeft (R := F) (S := F) (algebraMap D E₁ d)) =
      toΩ (algebraMap F T (algebraMap D F d))
    congr 1
    rw [IsScalarTower.algebraMap_apply D F E₁, AlgHom.commutes]
  ·
    refine { toRingHom := toΩ.comp (Algebra.TensorProduct.includeRight (R := F) (A := E₁) (B := E₂)).toRingHom,
      commutes' := fun d => ?_ }
    show toΩ (Algebra.TensorProduct.includeRight (R := F) (A := E₁) (algebraMap D E₂ d)) =
      toΩ (algebraMap F T (algebraMap D F d))
    congr 1
    rw [IsScalarTower.algebraMap_apply D F E₂, AlgHom.commutes]


-- created on 2026-10-20
