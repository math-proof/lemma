import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Instance.CohCarrier_HeckeData
import Structure.CohCarrier_HeckeData
import Abbrev.CohCarrier_HeckeData

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w


namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

noncomputable def thetaTilde : D.FreeAlg →ₐ[𝒪] k := MvPolynomial.aeval D.θbar

def mTheta : Ideal D.FreeAlg := RingHom.ker D.thetaTilde.toRingHom

noncomputable def opSubalgebra : Subalgebra 𝒪 (Module.End 𝒪 V) := Algebra.adjoin 𝒪 (Set.range D.op)

theorem op_comm_of_mem : ∀ a ∈ Set.range D.op, ∀ b ∈ Set.range D.op, a * b = b * a := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  exact D.comm g h

open scoped IsMulCommutative

noncomputable def opAlgHom : D.FreeAlg →ₐ[𝒪] Module.End 𝒪 V :=
  (D.opSubalgebra.val).comp
    (MvPolynomial.aeval fun g => (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ :
      ↥D.opSubalgebra))

@[simp] theorem opAlgHom_X (g : D.Gen) : D.opAlgHom (MvPolynomial.X g) = D.op g := by
  simp [opAlgHom]

@[reducible] noncomputable def moduleFreeAlg : Module D.FreeAlg V :=
  Module.compHom V D.opAlgHom.toRingHom

attribute [local instance] moduleFreeAlg

noncomputable abbrev ML : Type (max u v) := LocalizedModule D.mTheta.primeCompl V

example : AddCommGroup D.ML := inferInstance
example : Module (Localization D.mTheta.primeCompl) D.ML := inferInstance
example : Module D.FreeAlg D.ML := inferInstance

noncomputable def toML : V →ₗ[D.FreeAlg] D.ML := LocalizedModule.mkLinearMap D.mTheta.primeCompl V

theorem algebraMap_freeAlg_smul (r : 𝒪) (v : V) : (algebraMap 𝒪 D.FreeAlg r) • v = r • v := by
  show D.opAlgHom (algebraMap 𝒪 D.FreeAlg r) v = r • v
  rw [AlgHom.commutes]
  rfl

example : Module 𝒪 D.ML := inferInstance

example : IsScalarTower 𝒪 (Localization D.mTheta.primeCompl) D.ML := inferInstance

example : IsScalarTower 𝒪 D.FreeAlg D.ML := inferInstance

noncomputable def toMLₒ : V →ₗ[𝒪] D.ML := D.toML.restrictScalars 𝒪

@[simp] theorem toMLₒ_apply (v : V) : D.toMLₒ v = D.toML v := rfl

end HeckeData

end CohCarrier

end
