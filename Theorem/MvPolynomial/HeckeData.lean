module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Instance.CohCarrier_HeckeData
public import Structure.CohCarrier_HeckeData
public import Abbrev.CohCarrier_HeckeData

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w


namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)


public theorem op_comm_of_mem : ∀ a ∈ Set.range D.op, ∀ b ∈ Set.range D.op, a * b = b * a := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  exact D.comm g h

open scoped IsMulCommutative


@[simp] public theorem opAlgHom_X (g : D.Gen) : D.opAlgHom (MvPolynomial.X g) = D.op g := by
  simp [opAlgHom]


public theorem algebraMap_freeAlg_smul (r : 𝒪) (v : V) : (algebraMap 𝒪 D.FreeAlg r) • v = r • v := by
  show D.opAlgHom (algebraMap 𝒪 D.FreeAlg r) v = r • v
  rw [AlgHom.commutes]
  rfl

example : Module 𝒪 D.ML := inferInstance

example : IsScalarTower 𝒪 (Localization D.mTheta.primeCompl) D.ML := inferInstance

example : IsScalarTower 𝒪 D.FreeAlg D.ML := inferInstance


@[simp] public theorem toMLₒ_apply (v : V) : D.toMLₒ v = D.toML v := rfl

end HeckeData

end CohCarrier

end
