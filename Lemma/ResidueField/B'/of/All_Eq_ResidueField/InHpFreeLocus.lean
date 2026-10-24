import Mathlib
import sympy.Basic
open TensorProduct


/--
[Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor.lean)
-/
@[path]
private lemma main
  [Finite ι]
  {T : Type u} [CommRing T]
  {M : Type u} [AddCommGroup M] [Module T M] [Module.FinitePresentation T M]
  {p : Ideal T} [hp : p.IsPrime]
  {m : ι → M}
  {b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M)}
-- given
  (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
  (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
-- imply
  ∃ (t : T) (_ : t ∉ p)
    (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
    ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) := by
-- proof
  classical
    set R := Localization.AtPrime p with hR
    set Mp := LocalizedModule p.primeCompl M with hMp
    set fM : M →ₗ[T] Mp := LocalizedModule.mkLinearMap p.primeCompl M with hfM
    have : Module.Free R Mp := Module.mem_freeLocus.mp hfree
    have : Module.FinitePresentation R Mp := inferInstance
    let κ := p.ResidueField
    have hbc : IsBaseChange R fM := IsLocalizedModule.isBaseChange p.primeCompl R fM
    let E : κ ⊗[T] M ≃ₗ[κ] κ ⊗[R] Mp :=
      (AlgebraTensorModule.cancelBaseChange T R κ κ M).symm ≪≫ₗ
        AlgebraTensorModule.congr (LinearEquiv.refl κ κ) hbc.equiv
    have hE : ∀ x : M, E ((1 : κ) ⊗ₜ[T] x) = (1 : κ) ⊗ₜ[R] fM x := by
      intro x
      simp only [E, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.congr_tmul,
        LinearEquiv.refl_apply, IsBaseChange.equiv_tmul, one_smul]
    let bp : Module.Basis ι κ (κ ⊗[R] Mp) := b.map E
    have hbp : ∀ i, bp i = (TensorProduct.mk R κ Mp 1 ∘ fun i => fM (m i)) i := by
      intro i
      simp only [bp, Module.Basis.map_apply, hb, hE, Function.comp_apply, TensorProduct.mk_apply]
    have hfun : (⇑bp : ι → κ ⊗[R] Mp) = TensorProduct.mk R κ Mp 1 ∘ fun i => fM (m i) := funext hbp
    obtain ⟨B, hB⟩ := Module.exists_basis_of_basis_baseChange (R := R) (M := Mp) (fun i => fM (m i))
      (by rw [← hfun]; apply bp.linearIndependent) (by rw [← hfun]; apply bp.span_eq)
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
    have : Fintype ι := Fintype.ofFinite ι
    have : Module.FinitePresentation T (ι →₀ T) := Module.finitePresentation_of_projective _ _
    have : Module.Finite T (ι →₀ T) := inferInstance
    set L : (ι →₀ T) →ₗ[T] M := Finsupp.linearCombination T m with hL
    set fF : (ι →₀ T) →ₗ[T] (ι →₀ R) := Finsupp.mapRange.linearMap (α := ι) (Algebra.linearMap T R) with hfF
    let ψ : (ι →₀ R) ≃ₗ[R] Mp := (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).equiv B (Equiv.refl ι)
    have hψ : ∀ i, ψ (Finsupp.single i 1) = B i := fun i => by
      have h := Module.Basis.equiv_apply (b := (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R))) (b' := B)
        (i := i) (e := Equiv.refl ι)
      simp only [Finsupp.coe_basisSingleOne, Equiv.refl_apply] at h
      exact h
    have hmap : IsLocalizedModule.map p.primeCompl fF fM L = ψ.toLinearMap.restrictScalars T := by
      apply IsLocalizedModule.ext p.primeCompl fF (IsLocalizedModule.map_units fM)
      rw [IsLocalizedModule.map_comp]
      apply Finsupp.lhom_ext
      intro i c
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hL,
        Finsupp.linearCombination_single, map_smul, hfF, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
        Algebra.linearMap_apply, ← Finsupp.smul_single_one, LinearEquiv.map_smul, hψ, hB, algebraMap_smul]
    have hbij : Function.Bijective (IsLocalizedModule.map p.primeCompl fF fM L) := by
      rw [hmap]; apply ψ.bijective
    obtain ⟨t, ht, hLt⟩ := Module.FinitePresentation.exists_notMem_bijective (M := ι →₀ T) (N := M) L p fF fM hbij
    let et := LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers t) L) hLt
    let bt₀ : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) (ι →₀ T)) :=
      Module.Basis.ofIsLocalizedModule (Localization.Away t) (Submonoid.powers t)
        (LocalizedModule.mkLinearMap (Submonoid.powers t) (ι →₀ T)) Finsupp.basisSingleOne
    refine ⟨t, ht, bt₀.map et, fun i => ?_⟩
    rw [Module.Basis.map_apply, Module.Basis.ofIsLocalizedModule_apply, Finsupp.coe_basisSingleOne, LinearEquiv.ofBijective_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, hL,
      Finsupp.linearCombination_single, one_smul]


-- created on 2026-10-23
