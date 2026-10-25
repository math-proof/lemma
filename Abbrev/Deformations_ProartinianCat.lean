import Mathlib
import Instance.Deformations_IsProartinian
import Class.Deformations_IsResidueAlgebra
import Instance.Deformations_ProartinianCat
import Class.Deformations_ProartinianCat
import Structure.Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u) [CommRing 𝓞]

section 𝓞_is_local

end 𝓞_is_local


local notation3:max "𝓒" 𝓞 => ProartinianCat 𝓞

namespace ProartinianCat


abbrev of (X : Type u) [CommRing X] [Algebra 𝓞 X]
    [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X] :
    ProartinianCat 𝓞 :=
  ⟨X⟩


variable {𝓞} in

abbrev ofHom {A B : Type u}
    [CommRing A] [Algebra 𝓞 A] [TopologicalSpace A] [IsLocalProartinianAlgebra 𝓞 A]
    [CommRing B] [Algebra 𝓞 B] [TopologicalSpace B] [IsLocalProartinianAlgebra 𝓞 B]
    (f : A →A[𝓞] B) :
    of 𝓞 A ⟶ of 𝓞 B := ⟨f⟩

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

end residueField

end ProartinianCat

end Deformation
