-- Carved from Lemma/Definitions/Def_CuspForm_AuxLevelHeckeModuleMid.lean: instance decls only.
import Instance.CuspForm_AuxLevelHeckeModule
import Abbrev.CuspForm_AuxLevelHeckeModuleMid

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

instance instModuleFreeAlgMidCarrier (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (hc₁ : MidOpComm N r S 𝒪) :
    Module (midHeckeData N r S 𝒪 θ hc₁).FreeAlg (CohCarrier.H1 (N * r) ⊤ 𝒪) :=
  (midHeckeData N r S 𝒪 θ hc₁).moduleFreeAlg

end CuspForm.AuxLevel

end
