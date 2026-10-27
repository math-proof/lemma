import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing Polynomial


attribute [local instance] Ideal.Quotient.field


/--
[Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.lean)
-/
@[path]
private lemma main
  {K₀ : Type u} [Field K₀]
  {𝒪 : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪] [Algebra K₀ 𝒪] [Algebra.EssFiniteType K₀ 𝒪] [Algebra.IsAlgebraic K₀ (ResidueField 𝒪)] [Algebra.IsSeparable K₀ (ResidueField 𝒪)]
  (u : 𝒪)
-- given
  (hu0 : u ≠ 0)
  (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
-- imply
  Algebra.FormallySmooth K₀ 𝒪 := by
-- proof
  classical
  let A : Subalgebra K₀ 𝒪 := Algebra.EssFiniteType.subalgebra K₀ 𝒪
  let M : Submonoid A := Algebra.EssFiniteType.submonoid K₀ 𝒪
  have hlocM : IsLocalization M 𝒪 := Algebra.EssFiniteType.isLocalization K₀ 𝒪
  obtain ⟨⟨a, sM⟩, has⟩ := IsLocalization.surj M u
  have hsunit : IsUnit (algebraMap A 𝒪 (sM : A)) := IsLocalization.map_units 𝒪 sM
  have hspan : maximalIdeal 𝒪 = Ideal.span {algebraMap A 𝒪 a} := by
    rw [hu, ← has]
    apply (Ideal.span_singleton_mul_right_unit hsunit u).symm
  have ha𝔪 : algebraMap A 𝒪 a ∈ maximalIdeal 𝒪 := hspan ▸ Ideal.mem_span_singleton_self _
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hu0
    have : u * algebraMap A 𝒪 (sM : A) = 0 := by
      rw [has, map_zero]
    apply (hsunit.mul_left_eq_zero).mp this
  let Q : Ideal A := (maximalIdeal 𝒪).comap (algebraMap A 𝒪)
  have hQprime : Q.IsPrime := Ideal.IsPrime.comap _
  have haQ : a ∈ Q := ha𝔪
  have hMQ : M = Q.primeCompl := by
    ext x
    change IsUnit (algebraMap A 𝒪 x) ↔ x ∉ Q
    change _ ↔ algebraMap A 𝒪 x ∉ maximalIdeal 𝒪
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hlocQ : IsLocalization.AtPrime 𝒪 Q := by
    change IsLocalization Q.primeCompl 𝒪
    rw [← hMQ]
    apply hlocM
  let eA : 𝒪 ≃ₐ[A] Localization.AtPrime Q := IsLocalization.algEquiv Q.primeCompl 𝒪 (Localization.AtPrime Q)
  let eK : 𝒪 ≃ₐ[K₀] Localization.AtPrime Q := eA.restrictScalars K₀
  have hQtop : Q ≠ ⊤ := hQprime.ne_top
  have ha : Transcendental K₀ a := by
    intro halg
    have hint : IsIntegral K₀ a := halg.isIntegral
    have hc : (minpoly K₀ a).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint ha0
    have h := minpoly.aeval K₀ a
    rw [← (minpoly K₀ a).X_mul_divX_add, map_add, map_mul, aeval_X, aeval_C] at h
    apply hQtop (Q.eq_top_of_isUnit_mem ((eq_neg_of_add_eq_zero_right h) ▸ Q.neg_mem (Q.mul_mem_right _ haQ)) ((IsUnit.mk0 _ hc).map _))
  let _ : Algebra K₀[X] A := (aeval a : K₀[X] →ₐ[K₀] A).toRingHom.toAlgebra
  have halg : ∀ f : K₀[X], algebraMap K₀[X] A f = aeval a f := fun _ => rfl
  have : IsScalarTower K₀ K₀[X] A :=
    IsScalarTower.of_algebraMap_eq fun k => ((aeval a).commutes k).symm
  have : IsScalarTower K₀ K₀[X] (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      rw [IsScalarTower.algebraMap_apply K₀ A (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply K₀ K₀[X] A]
  have : Module.IsTorsionFree K₀[X] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp ha)
  have : Module.Flat K₀[X] A := inferInstance
  have : Algebra.FiniteType K₀[X] A := Algebra.FiniteType.of_restrictScalars_finiteType K₀ K₀[X] A
  have : Algebra.FinitePresentation K₀[X] A := (Algebra.FinitePresentation.of_finiteType).mp ‹_›
  let ι : (A ⧸ Q) →ₐ[K₀] ResidueField 𝒪 :=
    Ideal.quotientMapₐ (maximalIdeal 𝒪) (IsScalarTower.toAlgHom K₀ A 𝒪) le_rfl
  have hι : Function.Injective ι := Ideal.quotientMap_injective
  have : Algebra.IsAlgebraic K₀ (A ⧸ Q) := Algebra.IsAlgebraic.of_injective ι hι
  have : Algebra.IsIntegral K₀ (A ⧸ Q) := Algebra.IsAlgebraic.isIntegral
  have hQmax : Q.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField' (Field.toIsField K₀))
  have : Algebra.IsSeparable K₀ (A ⧸ Q) := Algebra.IsSeparable.of_algHom _ _ ι
  have hXp : (X : K₀[X]) ∈ Q.under K₀[X] := by
    change algebraMap K₀[X] A X ∈ Q
    rwa [halg, aeval_X]
  have : (Q.under K₀[X]).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance fun h =>
      X_ne_zero ((Submodule.eq_bot_iff _).mp h X hXp)
  let _ : Algebra (Localization.AtPrime (Q.under K₀[X])) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver (Q.under K₀[X]) Q
  have hsep : Algebra.IsSeparable (K₀[X] ⧸ Q.under K₀[X]) (↥A ⧸ Q) :=
    Algebra.isSeparable_tower_top_of_isSeparable K₀ (K₀[X] ⧸ Q.under K₀[X]) (↥A ⧸ Q)
  have : Algebra.IsUnramifiedAt K₀[X] Q := by
    rw [Algebra.isUnramifiedAt_iff_map_eq (p := Q.under K₀[X])]
    refine ⟨Algebra.isSeparable_residueField_iff.mpr hsep, le_antisymm ?_ ?_⟩
    ·
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q)]
      apply (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hf
    ·
      intro z hz
      have hz' : eA.symm z ∈ maximalIdeal 𝒪 := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
        intro h
        apply hz
        rw [← AlgEquiv.apply_symm_apply (e := eA) z]
        apply h.map eA
      rw [hspan, Ideal.mem_span_singleton'] at hz'
      obtain ⟨r, hr⟩ := hz'
      have hz'' : z = eA r * algebraMap K₀[X] (Localization.AtPrime Q) X := by
        rw [IsScalarTower.algebraMap_apply K₀[X] A (Localization.AtPrime Q), halg, aeval_X,
          ← eA.commutes a, ← map_mul, hr, AlgEquiv.apply_symm_apply]
      rw [hz'']
      apply Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hXp)
  have : Algebra.IsEtaleAt K₀[X] Q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat Q
  have : Algebra.FormallySmooth K₀[X] (Localization.AtPrime Q) := inferInstance
  have : Algebra.FormallySmooth K₀ (Localization.AtPrime Q) :=
    Algebra.FormallySmooth.comp K₀ K₀[X] (Localization.AtPrime Q)
  apply Algebra.FormallySmooth.of_equiv eK.symm


-- created on 2026-10-13
