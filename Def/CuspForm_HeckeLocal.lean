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

def latticeRestrict {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)}
    (ht : t ∈ heckeAlgebra N 2 S) : Module.End ℤ ↥(intLattice N 2) :=
  LinearMap.restrict (t.restrictScalars ℤ)
    (fun _f hf => mem_intLattice_of_mem_heckeAlgebra one_le_two ht hf)

def latticeActionHom : ↥(heckeAlgebra N 2 S) →+* Module.End ℤ ↥(intLattice N 2) where
  toFun t := latticeRestrict N S t.2
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_zero' := LinearMap.ext fun _ => Subtype.ext rfl
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

def heckeLatticeAlgebra : Subalgebra ℤ (Module.End ℤ ↥(intLattice N 2)) :=
  ((latticeActionHom N S).toIntAlgHom).range


omit [NeZero N] in


omit [NeZero N] in


def latticeRestrictHom : ↥(heckeAlgebra N 2 S) →ₐ[ℤ] ↥(heckeLatticeAlgebra N S) :=
  ((latticeActionHom N S).toIntAlgHom).rangeRestrict


variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
variable (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)

def residualCharacter :
    (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) →ₐ[ℤ] IsLocalRing.ResidueField 𝒪 :=
  Algebra.TensorProduct.productMap
    (algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪)).toIntAlgHom θ.toIntAlgHom

def heckeCharKernel : Ideal (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :=
  RingHom.ker (residualCharacter N S 𝒪 θ)


def heckeBaseAlgebra : Type := 𝒪 ⊗[ℤ] ↥(heckeLatticeAlgebra N S)


def latticeBaseChange : (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) →+* heckeBaseAlgebra N S 𝒪 :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ 𝒪) (latticeRestrictHom N S)).toRingHom

def heckeLocalSubmonoid : Submonoid (heckeBaseAlgebra N S 𝒪) :=
  (heckeCharKernel N S 𝒪 θ).primeCompl.map (latticeBaseChange N S 𝒪)

def heckeLocal : Type :=
  Localization (heckeLocalSubmonoid N S 𝒪 θ)


def heckeLocal.π : ↥(heckeAlgebra N 2 S) →+* heckeLocal N S 𝒪 θ :=
  ((algebraMap (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)).comp (latticeBaseChange N S 𝒪)).comp
    Algebra.TensorProduct.includeRight.toRingHom

section Structure

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]


omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in


omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in


def heckeLocalIdeal : Ideal (heckeBaseAlgebra N S 𝒪) :=
  (heckeCharKernel N S 𝒪 θ).map (latticeBaseChange N S 𝒪)

end Structure

end CuspForm

end
