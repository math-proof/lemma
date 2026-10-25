-- Carved from Lemma/Definitions/Def_CuspForm_AuxLevelHeckeModule.lean: instance decls only.
import Lemma.CohCarrier.Inst
import Instance.CuspForm_HeckeAlgebra
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Abbrev.CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel

instance instModuleFreeAlgCarrier (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (hc : OpComm N r S 𝒪) : Module (heckeData N r S 𝒪 θ hc).FreeAlg (Carrier N r 𝒪) :=
  (heckeData N r S 𝒪 θ hc).moduleFreeAlg

end CuspForm.AuxLevel

end
