import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_algHom_residueField_ker_eq_of_isMaximal_of_finiteType.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsLocalRing A] [IsAlgClosed (ResidueField A)]
  {C : Type v} [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
  (y : Ideal C) [y.IsMaximal]
  -- given
  (hy : (maximalIdeal A).map (algebraMap A C) ≤ y) :
  -- imply
  ∃ ψ : C →ₐ[A] ResidueField A, RingHom.ker ψ.toRingHom = y := by
  -- proof
  classical
  let _ : Field (C ⧸ y) := Ideal.Quotient.field y
  have hker : ∀ a ∈ maximalIdeal A, ((Ideal.Quotient.mk y).comp (algebraMap A C)) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hy (Ideal.mem_map_of_mem _ ha)
  let f : RingHom (ResidueField A) (C ⧸ y) :=
    Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk y).comp (algebraMap A C)) hker
  have hf : ∀ a : A, f (residue A a) = Ideal.Quotient.mk y (algebraMap A C a) := fun a => rfl
  let _ : Algebra (ResidueField A) (C ⧸ y) := f.toAlgebra
  let _ : IsScalarTower A (ResidueField A) (C ⧸ y) :=
    IsScalarTower.of_algebraMap_eq (fun a => (hf a).symm)
  let _ : Algebra.FiniteType A (C ⧸ y) :=
    (‹Algebra.FiniteType A C›).of_surjective (Ideal.Quotient.mkₐ A y) (Ideal.Quotient.mkₐ_surjective A y)
  let _ : Algebra.FiniteType (ResidueField A) (C ⧸ y) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (ResidueField A) (C ⧸ y)
  let _ : Module.Finite (ResidueField A) (C ⧸ y) := finite_of_finite_type_of_isJacobsonRing (ResidueField A) (C ⧸ y)
  let _ : Algebra.IsIntegral (ResidueField A) (C ⧸ y) := Algebra.IsIntegral.of_finite (ResidueField A) (C ⧸ y)
  have hbij : Function.Bijective (algebraMap (ResidueField A) (C ⧸ y)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField A) (K := C ⧸ y)
  let e : RingEquiv (ResidueField A) (C ⧸ y) :=
    RingEquiv.ofBijective (algebraMap (ResidueField A) (C ⧸ y)) hbij
  have he : ∀ k : ResidueField A, e k = algebraMap (ResidueField A) (C ⧸ y) k := fun _ => rfl
  let ψ₀ : RingHom C (ResidueField A) := e.symm.toRingHom.comp (Ideal.Quotient.mk y)
  have hψ₀ : ∀ c : C, e (ψ₀ c) = Ideal.Quotient.mk y c := fun c => e.apply_symm_apply _
  have hcomm : ∀ a : A, ψ₀ (algebraMap A C a) = algebraMap A (ResidueField A) a := by
    intro a
    apply e.injective
    rw [hψ₀, he]
    show Ideal.Quotient.mk y (algebraMap A C a) = f (algebraMap A (ResidueField A) a)
    apply (hf a).symm
  refine ⟨⟨ψ₀, hcomm⟩, ?_⟩
  ext c
  rw [RingHom.mem_ker]
  show ψ₀ c = 0 ↔ c ∈ y
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hψ₀, map_eq_zero_iff _ e.injective]


-- created on 2026-10-20
