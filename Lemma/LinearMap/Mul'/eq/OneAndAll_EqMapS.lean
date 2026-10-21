import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {S T : Type} [CommRing S] [CommRing T] (σ : S →+* T) {Λ : Type} [Ring Λ]
private lemma exists_sepElt_baseChange_of_surjective (hσ : Function.Surjective σ)
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e) :
    ∃ eT : (T ⊗[ℤ] Λ) ⊗[T] (T ⊗[ℤ] Λ),
      LinearMap.mul' T (T ⊗[ℤ] Λ) eT = 1 ∧
      ∀ x : T ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft T x) LinearMap.id eT =
        TensorProduct.map LinearMap.id (LinearMap.mulRight T x) eT := by
  classical
  let _ : Algebra S T := σ.toAlgebra
  let r : S ⊗[ℤ] Λ →ₐ[S] T ⊗[ℤ] Λ :=
    Algebra.TensorProduct.lift (Algebra.ofId S (T ⊗[ℤ] Λ)) (Algebra.TensorProduct.includeRight (R := ℤ) (A := T) (B := Λ))
      (fun s l => by
        show algebraMap S (T ⊗[ℤ] Λ) s * _ = _ * algebraMap S (T ⊗[ℤ] Λ) s
        exact (Algebra.commutes s _))
  have hr : ∀ (s : S) (l : Λ), r (s ⊗ₜ l) = σ s ⊗ₜ l := by
    intro s l
    rw [Algebra.TensorProduct.lift_tmul]
    show algebraMap S (T ⊗[ℤ] Λ) s * ((1 : T) ⊗ₜ[ℤ] l) = σ s ⊗ₜ l
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hrsurj : Function.Surjective r := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero r⟩
    | tmul t l => obtain ⟨s, rfl⟩ := hσ t; exact ⟨s ⊗ₜ l, hr s l⟩
    | add y₁ y₂ h₁ h₂ => obtain ⟨z₁, rfl⟩ := h₁; obtain ⟨z₂, rfl⟩ := h₂; exact ⟨z₁ + z₂, map_add r z₁ z₂⟩
  let F : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ) →ₗ[S] (T ⊗[ℤ] Λ) ⊗[T] (T ⊗[ℤ] Λ) :=
    TensorProduct.lift
      (LinearMap.mk₂ S (fun a a' => r a ⊗ₜ[T] r a')
        (fun a₁ a₂ a' => by
          show r (a₁ + a₂) ⊗ₜ[T] r a' = r a₁ ⊗ₜ[T] r a' + r a₂ ⊗ₜ[T] r a'
          rw [map_add, TensorProduct.add_tmul])
        (fun s a a' => by
          show r (s • a) ⊗ₜ[T] r a' = s • (r a ⊗ₜ[T] r a')
          rw [map_smul, TensorProduct.smul_tmul'])
        (fun a a₁ a₂ => by
          show r a ⊗ₜ[T] r (a₁ + a₂) = r a ⊗ₜ[T] r a₁ + r a ⊗ₜ[T] r a₂
          rw [map_add, TensorProduct.tmul_add])
        (fun s a a' => by
          show r a ⊗ₜ[T] r (s • a') = s • (r a ⊗ₜ[T] r a')
          rw [map_smul, TensorProduct.tmul_smul]))
  have hF : ∀ a a', F (a ⊗ₜ a') = r a ⊗ₜ[T] r a' := fun a a' => by
    show TensorProduct.lift _ (a ⊗ₜ a') = _
    rw [TensorProduct.lift.tmul]; rfl
  have hmul : ∀ z, LinearMap.mul' T (T ⊗[ℤ] Λ) (F z) = r (LinearMap.mul' S (S ⊗[ℤ] Λ) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, map_zero]
    | tmul a a' => rw [hF, LinearMap.mul'_apply, LinearMap.mul'_apply]; exact (map_mul r a a').symm
    | add z₁ z₂ h₁ h₂ => rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, map_add, h₁, h₂]
  have hleft : ∀ y z, TensorProduct.map (LinearMap.mulLeft T (r y)) LinearMap.id (F z) =
      F (TensorProduct.map (LinearMap.mulLeft S y) LinearMap.id z) := by
    intro y z
    induction z using TensorProduct.induction_on with
    | zero => rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
    | tmul a a' =>
      rw [hF, TensorProduct.map_tmul, TensorProduct.map_tmul, hF, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.id_apply, LinearMap.id_apply, map_mul r y a]
    | add z₁ z₂ h₁ h₂ => rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, h₁, h₂]
  have hright : ∀ y z, TensorProduct.map LinearMap.id (LinearMap.mulRight T (r y)) (F z) =
      F (TensorProduct.map LinearMap.id (LinearMap.mulRight S y) z) := by
    intro y z
    induction z using TensorProduct.induction_on with
    | zero => rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
    | tmul a a' =>
      rw [hF, TensorProduct.map_tmul, TensorProduct.map_tmul, hF, LinearMap.mulRight_apply, LinearMap.mulRight_apply,
        LinearMap.id_apply, LinearMap.id_apply, map_mul r a' y]
    | add z₁ z₂ h₁ h₂ => rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, h₁, h₂]
  refine ⟨F e, ?_, ?_⟩
  · rw [hmul, he₁, map_one]
  · intro x
    obtain ⟨y, rfl⟩ := hrsurj x
    rw [hleft, hright, he₂]
/--
[IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement.lean)
-/
@[path]
private lemma main
    (S : Type) [CommRing S] [IsLocalRing S] {Λ : Type} [Ring Λ]
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e) :
    ∃ eΛ : ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ) ⊗[(IsLocalRing.ResidueField S)] ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ),
      LinearMap.mul' (IsLocalRing.ResidueField S) ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ) eΛ = 1 ∧
      ∀ x : (IsLocalRing.ResidueField S) ⊗[ℤ] Λ,
        TensorProduct.map (LinearMap.mulLeft (IsLocalRing.ResidueField S) x) LinearMap.id eΛ =
          TensorProduct.map LinearMap.id (LinearMap.mulRight (IsLocalRing.ResidueField S) x) eΛ :=
  exists_sepElt_baseChange_of_surjective (IsLocalRing.residue S) IsLocalRing.residue_surjective e he₁ he₂

-- created on 2026-10-20
