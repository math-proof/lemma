module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Instance.CohCarrier_HeckeData
public import Structure.CohCarrier_HeckeData
public import Abbrev.CohCarrier_HeckeData

@[expose] public section

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

open scoped IsMulCommutative

noncomputable def opAlgHom : D.FreeAlg →ₐ[𝒪] Module.End 𝒪 V :=
  (D.opSubalgebra.val).comp
    (MvPolynomial.aeval fun g => (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ :
      ↥D.opSubalgebra))

@[reducible] noncomputable def moduleFreeAlg : Module D.FreeAlg V :=
  Module.compHom V D.opAlgHom.toRingHom

attribute [local instance] moduleFreeAlg

noncomputable abbrev ML : Type (max u v) := LocalizedModule D.mTheta.primeCompl V

noncomputable def toML : V →ₗ[D.FreeAlg] D.ML := LocalizedModule.mkLinearMap D.mTheta.primeCompl V

noncomputable def toMLₒ : V →ₗ[𝒪] D.ML := D.toML.restrictScalars 𝒪

end HeckeData

end CohCarrier

end

end
