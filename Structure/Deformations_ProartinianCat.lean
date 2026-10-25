import Mathlib
import Instance.Deformations_IsProartinian
import Class.Deformations_IsResidueAlgebra
import Instance.Deformations_ProartinianCat
import Class.Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u) [CommRing 𝓞]

section 𝓞_is_local


end 𝓞_is_local

structure ProartinianCat where

  carrier : Type u

  [commRing : CommRing carrier]

  [topologicalSpace : TopologicalSpace carrier]

  [algebra : Algebra 𝓞 carrier]
  [isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 carrier]


namespace ProartinianCat

attribute [instance] commRing algebra topologicalSpace isLocalProartinianAlgebra

initialize_simps_projections ProartinianCat (-commRing, -algebra, -topologicalSpace)

attribute [coe] ProartinianCat.carrier


variable {𝓞} in

@[ext]
structure Hom (A B : ProartinianCat 𝓞) where

  hom : A →A[𝓞] B

variable {𝓞} in


variable {𝓞}

variable {X Y Z : Type u}
  [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X]
  [CommRing Y] [Algebra 𝓞 Y] [TopologicalSpace Y] [IsLocalProartinianAlgebra 𝓞 Y]
  [CommRing Z] [Algebra 𝓞 Z] [TopologicalSpace Z] [IsLocalProartinianAlgebra 𝓞 Z]

variable {A B C : ProartinianCat 𝓞}


section self

variable [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]


end self

section residueField

variable [IsLocalRing 𝓞]

set_option backward.isDefEq.respectTransparency false in


set_option backward.isDefEq.respectTransparency false in

noncomputable


end residueField

end ProartinianCat

end Deformation
