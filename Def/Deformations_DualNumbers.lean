import Mathlib
import Class.Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

namespace Deformation

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]


noncomputable def dualNumbers : ProartinianCat 𝓞 :=
  .of 𝓞 ((𝓴 𝓞)[ε])


noncomputable def dualNumbersFst : dualNumbers 𝓞 ⟶ residueField where
  hom := ⟨TrivSqZeroExt.fstHom 𝓞 (𝓴 𝓞) (𝓴 𝓞), continuous_of_discreteTopology⟩

end ProartinianCat

end Deformation
