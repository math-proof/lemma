import Instance.CohCarrier_Level
import Structure.HeckeModule_IharaRungDatum
import Structure.HeckeModule_IharaDataAt
import Structure.CohCarrier_LevelPairing

set_option autoImplicit false

namespace IharaTower

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]


namespace CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]

abbrev cornerRing (cd : CornerData (𝒪 := 𝒪) 𝕋 V) : Type := cd.split.CornerRing cd.idx

abbrev cornerModule (cd : CornerData (𝒪 := 𝒪) 𝕋 V) : Type :=
  ↥(cornerSubmodule (M := V) (cd.split.e cd.idx))

end CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋']
variable {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋' V']


namespace DegeneracyDescent

variable {cd : CornerData (𝒪 := 𝒪) 𝕋 V} {cd' : CornerData (𝒪 := 𝒪) 𝕋' V'} {n : ℕ}

end DegeneracyDescent

open CohCarrier in

abbrev H1CornerData (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type) [AddCommGroup A] [Module 𝒪 A]
    (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M H A)]
    [IsScalarTower 𝒪 𝕋 (H1 M H A)] : Type :=
  CornerData (𝒪 := 𝒪) 𝕋 (H1 M H A)

end IharaTower
