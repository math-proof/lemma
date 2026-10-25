import Structure.CuspForm_HeckeGaloisRepDatum
import Def.CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite
import Def.CuspForm_HeckeLocal

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace CuspForm

variable (N : ℕ) [NeZero N] (S : Set ℕ)


theorem intLattice.moduleFinite : Module.Finite ℤ ↥(intLattice N 2) :=
  Module.Finite.iff_fg.mpr (intLattice_fg N 2)

omit [NeZero N] in

theorem isAddTorsionFree_cuspForm : IsAddTorsionFree (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  .of_isTorsionFree ℂ _

theorem intLattice.moduleFree : Module.Free ℤ ↥(intLattice N 2) := by
  haveI := intLattice.moduleFinite N
  haveI := isAddTorsionFree_cuspForm N
  exact Module.free_of_finite_type_torsion_free'

omit [NeZero N] in

theorem intLattice.isAddTorsionFree_end : IsAddTorsionFree (Module.End ℤ ↥(intLattice N 2)) where
  nsmul_right_injective n hn a b hab := by
    haveI := isAddTorsionFree_cuspForm N
    refine LinearMap.ext fun f => Subtype.ext ?_
    have h : n • ((a f : ↥(intLattice N 2)) : CuspForm (CongruenceSubgroup.Gamma0 N) 2) =
        n • ((b f : ↥(intLattice N 2)) : CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
      simpa using congrArg (fun g : Module.End ℤ ↥(intLattice N 2) =>
        ((g f : ↥(intLattice N 2)) : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) hab
    exact nsmul_right_injective hn h


theorem heckeLatticeAlgebra.isAddTorsionFree : IsAddTorsionFree ↥(heckeLatticeAlgebra N S) where
  nsmul_right_injective n hn a b hab := by
    haveI := intLattice.isAddTorsionFree_end N
    apply Subtype.ext
    have h : n • (a : Module.End ℤ ↥(intLattice N 2)) = n • (b : Module.End ℤ ↥(intLattice N 2)) :=
      congrArg Subtype.val hab
    exact nsmul_right_injective hn h


theorem latticeRestrict_injective (hint : HasIntegralStructure N 2)
    (t : ↥(heckeAlgebra N 2 S)) (h : latticeRestrict N S t.2 = 0) : t = 0 := by
  refine Subtype.ext (LinearMap.ext_on hint fun f hf => ?_)
  exact congrArg Subtype.val (LinearMap.congr_fun h ⟨f, hf⟩)

set_option synthInstance.maxHeartbeats 400000 in
theorem latticeActionHom_injective (hint : HasIntegralStructure N 2) :
    Function.Injective (latticeActionHom N S) :=
  (injective_iff_map_eq_zero _).mpr fun t ht => latticeRestrict_injective N S hint t ht

theorem latticeRestrictHom_surjective : Function.Surjective (latticeRestrictHom N S) :=
  AlgHom.rangeRestrict_surjective _

theorem latticeRestrictHom_bijective (hint : HasIntegralStructure N 2) :
    Function.Bijective (latticeRestrictHom N S) :=
  ⟨fun _ _ h => latticeActionHom_injective N S hint (congrArg Subtype.val h),
    latticeRestrictHom_surjective N S⟩

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
variable (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)


section Structure

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]

theorem residualCharacter_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    residualCharacter N S 𝒪 θ (a ⊗ₜ t) = IsLocalRing.residue 𝒪 a * θ t := rfl

theorem residualCharacter_algebraMap (a : 𝒪) :
    residualCharacter N S 𝒪 θ (algebraMap 𝒪 _ a) = IsLocalRing.residue 𝒪 a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    residualCharacter_tmul, map_one, mul_one]

theorem residualCharacter_surjective : Function.Surjective (residualCharacter N S 𝒪 θ) :=
  fun x => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap 𝒪 _ a, residualCharacter_algebraMap N S 𝒪 θ a⟩


theorem mem_heckeCharKernel_iff (x : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :
    x ∈ heckeCharKernel N S 𝒪 θ ↔ residualCharacter N S 𝒪 θ x = 0 := RingHom.mem_ker

theorem algebraMap_mem_heckeCharKernel_iff (a : 𝒪) :
    algebraMap 𝒪 (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) a ∈ heckeCharKernel N S 𝒪 θ ↔
      a ∈ IsLocalRing.maximalIdeal 𝒪 := by
  rw [mem_heckeCharKernel_iff, residualCharacter_algebraMap, IsLocalRing.residue_eq_zero_iff]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem latticeBaseChange_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    latticeBaseChange N S 𝒪 (a ⊗ₜ t) =
      (a ⊗ₜ[ℤ] latticeRestrictHom N S t : 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)) := rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem latticeBaseChange_algebraMap (a : 𝒪) :
    latticeBaseChange N S 𝒪 (algebraMap 𝒪 _ a) = algebraMap 𝒪 (heckeBaseAlgebra N S 𝒪) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    latticeBaseChange_tmul, map_one]
  rfl

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem latticeBaseChange_surjective : Function.Surjective (latticeBaseChange N S 𝒪) :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id (latticeRestrictHom_surjective N S)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem latticeBaseChange_injective (hint : HasIntegralStructure N 2) :
    Function.Injective (latticeBaseChange N S 𝒪) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : 𝒪 ≃ₐ[ℤ] 𝒪)
    (AlgEquiv.ofBijective (latticeRestrictHom N S) (latticeRestrictHom_bijective N S hint))).injective


theorem comap_heckeLocalIdeal
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ) :
    (heckeLocalIdeal N S 𝒪 θ).comap (latticeBaseChange N S 𝒪) = heckeCharKernel N S 𝒪 θ := by
  rw [heckeLocalIdeal, Ideal.comap_map_of_surjective _ (latticeBaseChange_surjective N S 𝒪),
    sup_eq_left]
  exact hker

theorem heckeLocalIdeal_isMaximal
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ) :
    (heckeLocalIdeal N S 𝒪 θ).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ (latticeBaseChange_surjective N S 𝒪)
    (heckeCharKernel.instIsMaximal N S 𝒪 θ)).resolve_left fun htop => ?_
  apply (heckeCharKernel.instIsMaximal N S 𝒪 θ).ne_top
  rw [← comap_heckeLocalIdeal N S 𝒪 θ hker, heckeLocalIdeal, htop, Ideal.comap_top]

theorem mem_heckeLocalSubmonoid_iff
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ)
    (x : heckeBaseAlgebra N S 𝒪) :
    x ∈ heckeLocalSubmonoid N S 𝒪 θ ↔ x ∉ heckeLocalIdeal N S 𝒪 θ := by
  constructor
  · rintro ⟨a, ha, rfl⟩ hx
    refine Ideal.mem_primeCompl_iff.mp ha ?_
    rw [← comap_heckeLocalIdeal N S 𝒪 θ hker]
    exact Ideal.mem_comap.mpr hx
  · intro hx
    obtain ⟨a, rfl⟩ := latticeBaseChange_surjective N S 𝒪 x
    exact ⟨a, Ideal.mem_primeCompl_iff.mpr fun ha => hx (Ideal.mem_map_of_mem _ ha), rfl⟩

section Hint

variable [Fact (HasIntegralStructure N 2)]

theorem ker_latticeBaseChange_le_heckeCharKernel :
    RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ := fun x hx => by
  rw [RingHom.mem_ker] at hx
  rw [latticeBaseChange_injective N S 𝒪 Fact.out (hx.trans (map_zero _).symm)]
  exact zero_mem _


theorem heckeLocalSubmonoid_eq_primeCompl :
    heckeLocalSubmonoid N S 𝒪 θ = (heckeLocalIdeal N S 𝒪 θ).primeCompl :=
  Submonoid.ext fun x =>
    (mem_heckeLocalSubmonoid_iff N S 𝒪 θ (ker_latticeBaseChange_le_heckeCharKernel N S 𝒪 θ) x).trans
      Ideal.mem_primeCompl_iff.symm


theorem heckeLocal.isLocalRing : IsLocalRing (heckeLocal N S 𝒪 θ) :=
  IsLocalization.AtPrime.isLocalRing (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ)

theorem heckeLocal.isLocalHom_algebraMap : IsLocalHom (algebraMap 𝒪 (heckeLocal N S 𝒪 θ)) := by
  constructor
  intro a ha
  rw [IsScalarTower.algebraMap_apply 𝒪 (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ),
    IsLocalization.AtPrime.isUnit_to_map_iff (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ),
    Ideal.mem_primeCompl_iff, ← latticeBaseChange_algebraMap, ← Ideal.mem_comap,
    comap_heckeLocalIdeal N S 𝒪 θ (ker_latticeBaseChange_le_heckeCharKernel N S 𝒪 θ),
    algebraMap_mem_heckeCharKernel_iff] at ha
  exact IsLocalRing.notMem_maximalIdeal.mp ha

end Hint

end Structure

section TrioEngines

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private lemma trio_isTorsionFree_finsupp (R : Type) [CommRing R] (ι : Type) :
    Module.IsTorsionFree R (ι →₀ R) where
  isSMulRegular r hr f g hfg := Finsupp.ext fun a => hr.isSMulRegular (M := R) (by
    have h := congrArg (fun h => h a) hfg
    simpa [Finsupp.smul_apply] using h)

private lemma trio_isTorsionFree_of_free (R : Type) [CommRing R] (B : Type) [AddCommGroup B]
    [Module R B] [Module.Free R B] : Module.IsTorsionFree R B := by
  haveI := trio_isTorsionFree_finsupp R (Module.Free.ChooseBasisIndex R B)
  set b := Module.Free.chooseBasis R B with hb
  exact Function.Injective.moduleIsTorsionFree (⇑b.repr) b.repr.injective
    fun r m => map_smul b.repr r m

private lemma trio_surjective_atPrime {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (P : MaximalSpectrum B) :
    Function.Surjective (algebraMap B (Localization.AtPrime P.asIdeal)) := by
  classical
  obtain ⟨-, hbij, -, -⟩ := Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := R) B
  intro z
  obtain ⟨b, hb⟩ := hbij.2 (Function.update 0 P z)
  refine ⟨b, ?_⟩
  have h := congrFun hb P
  simp only [Function.update_self] at h
  exact h

private lemma trio_isTorsionFree_atPrime {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
    (P : MaximalSpectrum B) :
    Module.IsTorsionFree R (Localization.AtPrime P.asIdeal) := by
  classical
  obtain ⟨-, hbij, -, -⟩ := Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := R) B
  haveI htfB : Module.IsTorsionFree R B := trio_isTorsionFree_of_free R B
  set Φ : B →ₗ[R] ∀ Q : MaximalSpectrum B, Localization.AtPrime Q.asIdeal :=
    { toFun := fun a Q => algebraMap B (Localization.AtPrime Q.asIdeal) a
      map_add' := fun a b => funext fun Q => map_add _ a b
      map_smul' := fun c a => funext fun Q => by
        simp only [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply] } with hPhidef
  have hPhibij : Function.Bijective Φ := hbij
  have hsingle : Function.Injective
      (Pi.single (M := fun Q : MaximalSpectrum B => Localization.AtPrime Q.asIdeal) P) := by
    intro x y hxy
    have h := congrFun hxy P
    simpa using h
  set e := LinearEquiv.ofBijective Φ hPhibij with hedef
  set g : Localization.AtPrime P.asIdeal →ₗ[R] B :=
    e.symm.toLinearMap ∘ₗ
      LinearMap.single R (fun Q : MaximalSpectrum B => Localization.AtPrime Q.asIdeal) P
    with hgdef
  have hginj : Function.Injective g := e.symm.injective.comp hsingle
  exact Function.Injective.moduleIsTorsionFree (⇑g) hginj fun r m => map_smul g r m

private lemma trio_free_atPrime {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
    (P : MaximalSpectrum B) : Module.Free R (Localization.AtPrime P.asIdeal) := by
  obtain ⟨-, -, hfin, -⟩ := Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := R) B
  haveI := hfin P
  haveI := trio_isTorsionFree_atPrime (R := R) B P
  exact Module.free_of_finite_type_torsion_free'

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_moduleFinite_base : Module.Finite 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Module.Finite 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_moduleFree_base : Module.Free 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Module.Free 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_isNoetherianRing_base : IsNoetherianRing (heckeBaseAlgebra N S 𝒪) := by
  haveI := trio_moduleFinite_base N S 𝒪
  exact IsNoetherianRing.of_finite 𝒪 (heckeBaseAlgebra N S 𝒪)

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_subsingleton_or_ker_le :
    Subsingleton (heckeLocal N S 𝒪 θ) ∨
      RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ := by
  by_cases hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ
  · exact Or.inr hker
  · refine Or.inl ?_
    obtain ⟨x, hxk, hxm⟩ := SetLike.not_le_iff_exists.mp hker
    have h0 : (0 : heckeBaseAlgebra N S 𝒪) ∈ heckeLocalSubmonoid N S 𝒪 θ :=
      ⟨x, Ideal.mem_primeCompl_iff.mpr hxm, by
        rw [RingHom.mem_ker] at hxk
        exact hxk⟩
    exact IsLocalization.subsingleton h0

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in
private lemma trio_isLocalization_atPrime
    (hker : RingHom.ker (latticeBaseChange N S 𝒪) ≤ heckeCharKernel N S 𝒪 θ) :
    haveI := (heckeLocalIdeal_isMaximal N S 𝒪 θ hker).isPrime
    IsLocalization (heckeLocalIdeal N S 𝒪 θ).primeCompl (heckeLocal N S 𝒪 θ) := by
  haveI := (heckeLocalIdeal_isMaximal N S 𝒪 θ hker).isPrime
  have hsub : heckeLocalSubmonoid N S 𝒪 θ = (heckeLocalIdeal N S 𝒪 θ).primeCompl :=
    Submonoid.ext fun x => (mem_heckeLocalSubmonoid_iff N S 𝒪 θ hker x).trans
      Ideal.mem_primeCompl_iff.symm
  rw [← hsub]
  exact heckeLocal.instIsLocalization N S 𝒪 θ

end TrioEngines

end CuspForm

end
