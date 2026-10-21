import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]
variable {B : Type*} [CommRing B] [Algebra R B]
variable {K : Type*} [Field K] (O : ValuationSubring K)
variable {k : Type*} [Field k]
private lemma ker_eq_maximalIdeal (π : O →+* k) (hπ : Function.Surjective π) :
    RingHom.ker π = IsLocalRing.maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
private lemma algebraMap_surjective_of_isIntegral [IsAlgClosed K] {D : Type*} [CommRing D] [IsDomain D]
    [Algebra O D] [FaithfulSMul O D] [Algebra.IsIntegral O D] :
    Function.Surjective (algebraMap O D) := by
  let _ : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).mpr Subtype.val_injective
  let _ : Algebra.IsAlgebraic O D := Algebra.IsIntegral.isAlgebraic
  let f : D →ₐ[O] K := IsAlgClosed.lift
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have hker : (RingHom.ker f.toRingHom).comap (algebraMap O D) = ⊥ := by
      ext x
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        AlgHom.commutes, Ideal.mem_bot]
      exact ⟨fun h => by exact_mod_cast (map_eq_zero_iff _ Subtype.val_injective).mp h,
        fun h => by simp [h]⟩
    let _ : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime _
    have hbot := Ideal.eq_bot_of_comap_eq_bot (R := O) hker
    have hmem : d ∈ RingHom.ker f.toRingHom := hd
    rw [hbot, Ideal.mem_bot] at hmem
    exact hmem
  intro d
  have hint : IsIntegral O (f d) := (Algebra.IsIntegral.isIntegral d).map f
  obtain ⟨o, ho⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := K)).mp hint
  refine ⟨o, hf ?_⟩
  rw [AlgHom.commutes, ho]
variable [IsAlgClosed K] [Algebra R O] [Module.Finite R B] [Module.Flat R B]
private lemma exists_ringHom_comp_eq (π : O →+* k) (hπ : Function.Surjective π) (φ₀ : B →+* k)
    (hcomp : φ₀.comp (algebraMap R B) = π.comp (algebraMap R O)) :
    ∃ φ : B →+* O, φ.comp (algebraMap R B) = algebraMap R O ∧ π.comp φ = φ₀ := by
  classical
  let _ : Algebra O k := π.toAlgebra
  let _ : Algebra R k := (π.comp (algebraMap R O)).toAlgebra
  let _ : IsScalarTower R O k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : B →ₐ[R] k :=
    { toRingHom := φ₀
      commutes' := fun r => by
        change φ₀ (algebraMap R B r) = π (algebraMap R O r)
        exact congrArg (fun h : R →+* k => h r) hcomp }
  let ψ₀ : (O ⊗[R] B) →ₐ[O] k :=
    Algebra.TensorProduct.lift (Algebra.ofId O k) g (fun _ _ => Commute.all _ _)
  let 𝔪 : Ideal (O ⊗[R] B) := RingHom.ker ψ₀
  let h𝔪 : 𝔪.IsPrime := RingHom.ker_isPrime _
  have hunder : 𝔪.under O = IsLocalRing.maximalIdeal O := by
    rw [← ker_eq_maximalIdeal O π hπ]
    ext x
    simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, 𝔪]
    rw [show ψ₀ (algebraMap O (O ⊗[R] B) x) = π x from ψ₀.commutes x]
  let _ : 𝔪.LiesOver (IsLocalRing.maximalIdeal O) := ⟨hunder.symm⟩
  obtain ⟨P, hP𝔪, hP, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal O)) (q := IsLocalRing.maximalIdeal O) 𝔪
      bot_le
  let D := (O ⊗[R] B) ⧸ P
  have hinj : Function.Injective (algebraMap O D) := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    have : o ∈ P.under O := by
      rw [Ideal.under, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact ho
    rwa [← hPover.over, Ideal.mem_bot] at this
  let _ : FaithfulSMul O D := (faithfulSMul_iff_algebraMap_injective O D).mpr hinj
  let _ : Module.Finite O D :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O P).toLinearMap Ideal.Quotient.mk_surjective
  let _ : Algebra.IsIntegral O D := inferInstance
  have hsurj : Function.Surjective (algebraMap O D) := algebraMap_surjective_of_isIntegral O
  let e : O ≃+* D := RingEquiv.ofBijective (algebraMap O D) ⟨hinj, hsurj⟩
  let φ : B →+* O :=
    (e.symm : D →+* O).comp ((Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := B)).toRingHom)
  have hφ : ∀ b : B, algebraMap O D (φ b) = Ideal.Quotient.mk P ((1 : O) ⊗ₜ[R] b) := by
    intro b
    change e (e.symm _) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨φ, ?_, ?_⟩
  ·
    refine RingHom.ext fun r => ?_
    apply hinj
    rw [RingHom.comp_apply, hφ]
    change Ideal.Quotient.mk P (Algebra.TensorProduct.includeRight (algebraMap R B r)) =
      Ideal.Quotient.mk P (algebraMap O (O ⊗[R] B) (algebraMap R O r))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  ·
    refine RingHom.ext fun b => ?_
    rw [RingHom.comp_apply]
    have hmemP : (1 : O) ⊗ₜ[R] b - algebraMap O (O ⊗[R] B) (φ b) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hφ b]
      rfl
    have hmem𝔪 : (1 : O) ⊗ₜ[R] b - algebraMap O (O ⊗[R] B) (φ b) ∈ 𝔪 := hP𝔪 hmemP
    have h1 : ψ₀ ((1 : O) ⊗ₜ[R] b) = φ₀ b := by
      change Algebra.TensorProduct.lift _ _ _ _ = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    have h2 : ψ₀ (algebraMap O (O ⊗[R] B) (φ b)) = π (φ b) := ψ₀.commutes (φ b)
    have h3 : ψ₀ ((1 : O) ⊗ₜ[R] b - algebraMap O (O ⊗[R] B) (φ b)) = 0 := hmem𝔪
    rw [map_sub, h1, h2, sub_eq_zero] at h3
    exact h3.symm
/--
[ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat.lean)
-/
@[path]
private lemma main
    {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Flat R B]
    {K : Type*} [Field K] [IsAlgClosed K] (O : ValuationSubring K) [Algebra R ↥O]
    {k : Type*} [Field k] (π : ↥O →+* k) (hπ : Function.Surjective π)
    (φ₀ : B →+* k) (hcomp : φ₀.comp (algebraMap R B) = π.comp (algebraMap R ↥O)) :
    ∃ φ : B →+* ↥O, φ.comp (algebraMap R B) = algebraMap R ↥O ∧ π.comp φ = φ₀ :=
  exists_ringHom_comp_eq O π hπ φ₀ hcomp

-- created on 2026-10-21
