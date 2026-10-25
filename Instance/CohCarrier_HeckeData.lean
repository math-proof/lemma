-- Carved from Lemma/Definitions/Def_CohCarrier_HeckeData.lean: instance decls only.
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Lemma.CohCarrier.HeckeData

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w

namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]

instance mTheta_isPrime : D.mTheta.IsPrime := RingHom.ker_isPrime _

instance opSubalgebra_isMulCommutative : IsMulCommutative ↥D.opSubalgebra :=
  Algebra.isMulCommutative_adjoin 𝒪 D.op_comm_of_mem

open scoped IsMulCommutative


instance V_isScalarTower : IsScalarTower 𝒪 D.FreeAlg V :=
  ⟨fun r a v => by rw [Algebra.smul_def, mul_smul, algebraMap_freeAlg_smul]⟩

end HeckeData

end CohCarrier

end
