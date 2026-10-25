-- Carved from Lemma/Definitions/Def_WeierstrassCurve_VeluOrderTwoShortNF.lean: instance decls only.
import Mathlib
set_option autoImplicit false

namespace WeierstrassCurve

section KernelData

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]


instance instIsShortNFMk (a b : R) : (WeierstrassCurve.mk 0 0 0 a b).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

end KernelData

section ShortQuotient

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]

instance veluQuotient2_isShortNF (x₀ y₀ : R) : (W.veluQuotient2 x₀ y₀).IsShortNF where
  a₁ := a₁_of_isShortNF W
  a₂ := a₂_of_isShortNF W
  a₃ := a₃_of_isShortNF W


end ShortQuotient

end WeierstrassCurve
