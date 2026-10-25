import Instance.CuspForm_AuxLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.AuxLevel


abbrev midML (N r : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) (hc₁ : MidOpComm N r S 𝒪) :
    Type :=
  (midHeckeData N r S 𝒪 θ hc₁).ML

end CuspForm.AuxLevel

end
