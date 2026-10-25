import Instance.CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel


abbrev baseML (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₀ : BaseOpComm N r S 𝒪) :
    Type :=
  (baseHeckeData N r S 𝒪 θ hc₀).ML

end CuspForm.AuxLevel

end
