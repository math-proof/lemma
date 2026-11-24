-- Carved from Lemma/Definitions/Def_CohCarrier_HeckeData.lean: instance decls only.
module

public import Def.CohCarrier_HeckeData

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w

namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

instance mTheta_isPrime : D.mTheta.IsPrime := RingHom.ker_isPrime _

instance opSubalgebra_isMulCommutative : IsMulCommutative ↥D.opSubalgebra :=
  Algebra.isMulCommutative_adjoin 𝒪 (by
    rintro a ⟨g, rfl⟩ b ⟨h, rfl⟩ _
    exact D.comm g h)

open scoped IsMulCommutative

-- `Def` registers this only as a local instance; register it here so the `𝒪`-module on
-- `D.ML` and `IsScalarTower 𝒪 D.FreeAlg V` can be stated outside `Def`.
attribute [instance] moduleFreeAlg

instance V_isScalarTower : IsScalarTower 𝒪 D.FreeAlg V :=
  ⟨fun r a v => by
    rw [Algebra.smul_def, mul_smul]
    have h : D.opAlgHom (algebraMap 𝒪 D.FreeAlg r) (a • v) = r • (a • v) := by
      rw [AlgHom.commutes]
      rfl
    exact h⟩

end HeckeData

end CohCarrier

end
