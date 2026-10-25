-- Carved from Lemma/Definitions/Def_CuspForm_AuxLevelHeckeModuleBase.lean: instance decls only.
import Instance.CuspForm_AuxLevelHeckeModule
import Abbrev.CuspForm_AuxLevelHeckeModuleBase

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

instance instModuleFreeAlgBaseCarrier (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (hc₀ : BaseOpComm N r S 𝒪) :
    Module (baseHeckeData N r S 𝒪 θ hc₀).FreeAlg (CohCarrier.H1 N ⊤ 𝒪) :=
  (baseHeckeData N r S 𝒪 θ hc₀).moduleFreeAlg

end CuspForm.AuxLevel

end
