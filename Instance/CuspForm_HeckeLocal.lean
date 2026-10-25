-- Carved from Lemma/Definitions/Def_CuspForm_HeckeLocal.lean: instance decls only.
import Structure.CuspForm_HeckeGaloisRepDatum
import Def.CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace CuspForm

variable (N : ℕ) [NeZero N] (S : Set ℕ)


instance heckeLatticeAlgebra.instModuleFinite : Module.Finite ℤ ↥(heckeLatticeAlgebra N S) := by
  haveI := intLattice.moduleFinite N
  haveI := intLattice.moduleFree N
  exact Module.Finite.of_injective (heckeLatticeAlgebra N S).val.toLinearMap Subtype.val_injective


instance heckeLatticeAlgebra.instModuleFree : Module.Free ℤ ↥(heckeLatticeAlgebra N S) := by
  haveI := heckeLatticeAlgebra.isAddTorsionFree N S
  exact Module.free_of_finite_type_torsion_free'


instance heckeLatticeAlgebra.instCommRing : CommRing ↥(heckeLatticeAlgebra N S) :=
  { (inferInstance : Ring ↥(heckeLatticeAlgebra N S)) with
    mul_comm := by
      rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
      exact Subtype.ext ((map_mul _ s t).symm.trans ((congrArg _ (mul_comm s t)).trans (map_mul _ t s))) }


instance heckeCharKernel.instIsPrime : (heckeCharKernel N S 𝒪 θ).IsPrime :=
  RingHom.ker_isPrime _


instance heckeBaseAlgebra.instCommRing : CommRing (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (CommRing (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))

instance heckeBaseAlgebra.instAlgebra : Algebra 𝒪 (heckeBaseAlgebra N S 𝒪) :=
  inferInstanceAs (Algebra 𝒪 (𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)))


instance heckeLocal.instCommRing : CommRing (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (CommRing (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instAlgebra : Algebra 𝒪 (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (Algebra 𝒪 (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instAlgebraBase : Algebra (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (Algebra (heckeBaseAlgebra N S 𝒪) (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instIsScalarTower :
    IsScalarTower 𝒪 (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (IsScalarTower 𝒪 (heckeBaseAlgebra N S 𝒪) (Localization (heckeLocalSubmonoid N S 𝒪 θ)))

instance heckeLocal.instIsLocalization :
    IsLocalization (heckeLocalSubmonoid N S 𝒪 θ) (heckeLocal N S 𝒪 θ) :=
  inferInstanceAs (IsLocalization (heckeLocalSubmonoid N S 𝒪 θ) (Localization (heckeLocalSubmonoid N S 𝒪 θ)))


section Structure

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]


instance heckeCharKernel.instIsMaximal : (heckeCharKernel N S 𝒪 θ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (residualCharacter_surjective N S 𝒪 θ)


section Hint

variable [Fact (HasIntegralStructure N 2)]


instance heckeLocalIdeal.instIsMaximal : (heckeLocalIdeal N S 𝒪 θ).IsMaximal :=
  heckeLocalIdeal_isMaximal N S 𝒪 θ (ker_latticeBaseChange_le_heckeCharKernel N S 𝒪 θ)


instance heckeLocal.instIsLocalizationAtPrime :
    IsLocalization.AtPrime (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ) := by
  rw [IsLocalization.AtPrime, ← heckeLocalSubmonoid_eq_primeCompl N S 𝒪 θ]
  exact heckeLocal.instIsLocalization N S 𝒪 θ


end Hint

end Structure


instance heckeLocal.instIsNoetherianRing : IsNoetherianRing (heckeLocal N S 𝒪 θ) := by
  haveI := trio_isNoetherianRing_base N S 𝒪
  exact IsLocalization.isNoetherianRing (heckeLocalSubmonoid N S 𝒪 θ) (heckeLocal N S 𝒪 θ)
    inferInstance

instance heckeLocal.instModuleFinite : Module.Finite 𝒪 (heckeLocal N S 𝒪 θ) := by
  rcases trio_subsingleton_or_ker_le N S 𝒪 θ with hsub | hker
  · exact Module.Finite.of_surjective (0 : 𝒪 →ₗ[𝒪] heckeLocal N S 𝒪 θ)
      fun y => ⟨0, Subsingleton.elim _ _⟩
  · haveI := trio_moduleFinite_base N S 𝒪
    haveI hPmax : (heckeLocalIdeal N S 𝒪 θ).IsMaximal := heckeLocalIdeal_isMaximal N S 𝒪 θ hker
    haveI hloc := trio_isLocalization_atPrime N S 𝒪 θ hker
    obtain ⟨-, -, hfin, -⟩ := Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite (𝒪 := 𝒪)
      (heckeBaseAlgebra N S 𝒪)
    haveI := hfin ⟨heckeLocalIdeal N S 𝒪 θ, hPmax⟩
    have e := IsLocalization.algEquiv (heckeLocalIdeal N S 𝒪 θ).primeCompl
      (Localization.AtPrime (heckeLocalIdeal N S 𝒪 θ)) (heckeLocal N S 𝒪 θ)
    exact Module.Finite.equiv (e.toLinearEquiv.restrictScalars 𝒪)

instance heckeLocal.instModuleFree : Module.Free 𝒪 (heckeLocal N S 𝒪 θ) := by
  rcases trio_subsingleton_or_ker_le N S 𝒪 θ with hsub | hker
  · haveI := hsub
    exact Module.Free.of_subsingleton 𝒪 (heckeLocal N S 𝒪 θ)
  · haveI := trio_moduleFinite_base N S 𝒪
    haveI := trio_moduleFree_base N S 𝒪
    haveI hPmax : (heckeLocalIdeal N S 𝒪 θ).IsMaximal := heckeLocalIdeal_isMaximal N S 𝒪 θ hker
    haveI hloc := trio_isLocalization_atPrime N S 𝒪 θ hker
    haveI := trio_free_atPrime (R := 𝒪) (heckeBaseAlgebra N S 𝒪)
      ⟨heckeLocalIdeal N S 𝒪 θ, hPmax⟩
    have e := IsLocalization.algEquiv (heckeLocalIdeal N S 𝒪 θ).primeCompl
      (Localization.AtPrime (heckeLocalIdeal N S 𝒪 θ)) (heckeLocal N S 𝒪 θ)
    exact Module.Free.of_equiv (e.toLinearEquiv.restrictScalars 𝒪)

instance heckeLocal.instIsLocalRing [Fact (HasIntegralStructure N 2)] :
    IsLocalRing (heckeLocal N S 𝒪 θ) :=
  heckeLocal.isLocalRing N S 𝒪 θ

instance heckeLocal.instIsAdicComplete [Fact (HasIntegralStructure N 2)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (heckeLocal N S 𝒪 θ)) (heckeLocal N S 𝒪 θ) := by
  haveI := heckeLocal.isLocalHom_algebraMap N S 𝒪 θ
  exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)

instance heckeLocal.instIsLocalHom [Fact (HasIntegralStructure N 2)] :
    IsLocalHom (algebraMap 𝒪 (heckeLocal N S 𝒪 θ)) :=
  heckeLocal.isLocalHom_algebraMap N S 𝒪 θ

end CuspForm

end
