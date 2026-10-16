import Mathlib
import sympy.Basic
open Polynomial
open scoped TensorProduct nonZeroDivisors


private lemma includeRight_injective
  [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Module.Flat R S] :
-- imply
  Function.Injective (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) := by
-- proof
  have h1 : Function.Injective ((Algebra.linearMap R K).rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  intro a b hab
  have : (Algebra.linearMap R K).rTensor S ((TensorProduct.lid R S).symm a) =
      (Algebra.linearMap R K).rTensor S ((TensorProduct.lid R S).symm b) := by
    simpa [LinearMap.rTensor_tmul] using hab
  apply (TensorProduct.lid R S).symm.injective (h1 this)

private lemma exists_ne_zero_aeval_eq_zero
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite K (K ⊗[R] S)]
  {s : S} :
-- imply
  ∃ f : R[X], f ≠ 0 ∧ aeval s f = 0 := by
-- proof
  have hint : IsIntegral K ((1 : K) ⊗ₜ[R] s : K ⊗[R] S) := Algebra.IsIntegral.isIntegral _
  obtain ⟨g, hgmon, hg⟩ := hint
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors R) g, ?_, ?_⟩
  ·
    intro h0
    obtain ⟨b, hb, hbg⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) g
    rw [h0, Polynomial.map_zero] at hbg
    have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hc := congrArg (fun p : K[X] => p.coeff g.natDegree) hbg
    simp only [Polynomial.coeff_zero, Polynomial.coeff_smul, hgmon.coeff_natDegree] at hc
    apply hb0
    rw [Algebra.algebraMap_eq_smul_one]
    apply hc.symm
  ·
    apply includeRight_injective (R := R) (K := K)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply]
    apply IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors R) g hg

private lemma exists_aeval_eq_zero_not_forall_coeff_mem
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite K (K ⊗[R] S)]
  {P : Ideal R} {s : S}
-- given
  (hP : P ≠ ⊤) :
-- imply
  ∃ f : R[X], aeval s f = 0 ∧ ∃ i, f.coeff i ∉ P := by
-- proof
  classical
  let _ : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  let _ : NormalizedGCDMonoid R := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨f, hf0, hfs⟩ := exists_ne_zero_aeval_eq_zero (R := R) (K := K) (s := s)
  refine ⟨f.primPart, ?_, ?_⟩
  ·
    have hc : f.content ≠ 0 := by
      rwa [Ne, Polynomial.content_eq_zero_iff]
    have h1 : f.content • aeval s f.primPart = 0 := by
      rw [← hfs]
      conv_rhs => rw [Polynomial.eq_C_content_mul_primPart f]
      rw [map_mul, Polynomial.aeval_C, Algebra.smul_def]
    apply includeRight_injective (R := R) (K := K)
    rw [map_zero]
    have h2 := congrArg (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S) h1
    rw [map_smul, map_zero, ← IsScalarTower.algebraMap_smul K, smul_eq_zero] at h2
    obtain h2 | h2 := h2
    ·
      apply absurd h2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hc))
    ·
      apply h2
  ·
    by_contra hall
    push Not at hall
    obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal P).principal
    have hdvd : C π ∣ f.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := hall i
      rw [hπ, Ideal.submodule_span_eq, Ideal.mem_span_singleton'] at this
      obtain ⟨a, ha⟩ := this
      refine ⟨a, ?_⟩
      rw [← ha, mul_comm]
    have hu : IsUnit π :=
      (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp (Polynomial.isPrimitive_primPart f)) π hdvd
    apply hP
    rw [hπ, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    apply hu

private lemma isIntegral_quotient_map
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite K (K ⊗[R] S)]
  {P : Ideal R} [P.IsMaximal] :
-- imply
  Algebra.IsIntegral (R ⧸ P) (S ⧸ P.map (algebraMap R S)) := by
-- proof
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  refine ⟨fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, hfs, i, hi⟩ := exists_aeval_eq_zero_not_forall_coeff_mem (R := R) (K := K)
    (P := P) (s := s) (Ideal.IsMaximal.ne_top inferInstance)
  have hne : f.map (Ideal.Quotient.mk P) ≠ 0 := by
    intro h0
    apply hi
    have := congrArg (fun p => Polynomial.coeff p i) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    apply Ideal.Quotient.eq_zero_iff_mem.mp this
  apply isAlgebraic_iff_isIntegral.mp
  refine ⟨f.map (Ideal.Quotient.mk P), hne, ?_⟩
  have h1 : f.map (Ideal.Quotient.mk P) = f.map (algebraMap R (R ⧸ P)) := rfl
  rw [h1, Polynomial.aeval_map_algebraMap]
  change aeval (Ideal.Quotient.mkₐ R (P.map (algebraMap R S)) s) f = 0
  rw [Polynomial.aeval_algHom_apply, hfs, map_zero]


/--
[Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_QuasiFinite_of_flat_of_finiteType_of_moduleFinite_baseChange_fractionRing.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {S : Type w} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S] [Module.Finite K (K ⊗[R] S)] :
-- imply
  Algebra.QuasiFinite R S := by
-- proof
  classical
  refine ⟨fun P hP => ?_⟩
  if hP0 : P = ⊥ then
    subst hP0
    have hunit : ∀ y : nonZeroDivisors R, IsUnit (algebraMap R (⊥ : Ideal R).ResidueField (y : R)) := by
      intro y
      have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
        rw [Ideal.mem_primeCompl_iff, Ideal.mem_bot]
        apply nonZeroDivisors.ne_zero y.2
      rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).ResidueField]
      apply (IsLocalization.map_units (Localization.AtPrime (⊥ : Ideal R))
        (⟨(y : R), hy⟩ : (⊥ : Ideal R).primeCompl)).map _
    let _ : Algebra K (⊥ : Ideal R).ResidueField := (IsLocalization.lift (M := nonZeroDivisors R) hunit).toAlgebra
    let _ : IsScalarTower R K (⊥ : Ideal R).ResidueField :=
      IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors R) hunit r).symm)
    let e : (⊥ : Ideal R).ResidueField ⊗[K] (K ⊗[R] S) ≃ₐ[(⊥ : Ideal R).ResidueField]
      (⊥ : Ideal R).ResidueField ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R K _ _ S
    apply Module.Finite.of_surjective e.toLinearMap e.surjective
  else
    let _ : P.IsMaximal := hP.isMaximal hP0
    let _ : Field (R ⧸ P) := Ideal.Quotient.field P
    let _ : Algebra.IsIntegral (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
      isIntegral_quotient_map (K := K) (P := P)
    let _ : Algebra.FiniteType R (S ⧸ P.map (algebraMap R S)) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (P.map (algebraMap R S)))
        (Ideal.Quotient.mkₐ_surjective R _)
    let _ : Algebra.FiniteType (R ⧸ P) (S ⧸ P.map (algebraMap R S)) :=
      Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ P) _
    let _ : Module.Finite (R ⧸ P) (S ⧸ P.map (algebraMap R S)) := Algebra.IsIntegral.finite
    let _ : Module.Finite R (S ⧸ P.map (algebraMap R S)) := Module.Finite.trans (R ⧸ P) _
    let e₁ : (S ⧸ P.map (algebraMap R S)) ≃ₗ[R] (R ⧸ P) ⊗[R] S :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S P).toLinearEquiv.restrictScalars R).trans
        (Algebra.TensorProduct.comm R S (R ⧸ P)).toLinearEquiv
    let _ : Module.Finite R ((R ⧸ P) ⊗[R] S) := Module.Finite.of_surjective e₁.toLinearMap e₁.surjective
    let _ : Module.Finite (R ⧸ P) ((R ⧸ P) ⊗[R] S) := Module.Finite.of_restrictScalars_finite R (R ⧸ P) _
    let e₂ : P.ResidueField ⊗[R ⧸ P] ((R ⧸ P) ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R (R ⧸ P) _ _ S
    apply Module.Finite.of_surjective e₂.toLinearMap e₂.surjective


-- created on 2026-10-13
