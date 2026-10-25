import Mathlib
import Class.Deformations_ProartinianCat
import Structure.Deformations_ProartinianCat

set_option autoImplicit false

universe u

namespace Deformation

open CategoryTheory IsLocalRing ProartinianCat

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
variable {R : ProartinianCat 𝓞}

variable (R) in

noncomputable def residueMap (r : R) : 𝓴 𝓞 := (toResidueField R).hom r


variable (R) in

structure IsTangentVector (D : R → 𝓴 𝓞) : Prop where
  map_add : ∀ r s, D (r + s) = D r + D s
  leibniz : ∀ r s, D (r * s) = residueMap R r * D s + D r * residueMap R s
  map_algebraMap : ∀ o : 𝓞, D (algebraMap 𝓞 R o) = 0
  isLocallyConstant : IsLocallyConstant D

namespace IsTangentVector

variable {D : R → 𝓴 𝓞} (hD : IsTangentVector R D)

include hD


end IsTangentVector

variable (R) in


end ProartinianCat

end Deformation
