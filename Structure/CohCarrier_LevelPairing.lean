import Instance.CohCarrier_Level
import Structure.HeckeModule_IharaRungDatum
import Structure.HeckeModule_IharaDataAt

set_option autoImplicit false

namespace IharaTower

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]

structure CornerData (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋]
    (V : Type) [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V] : Type where
  split : IdempotentSplitting 𝕋
  idx : Fin split.n
  pairing : LevelPairing (𝒪 := 𝒪) (split.CornerRing idx)
    ↥(cornerSubmodule (M := V) (split.e idx))

namespace CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]


end CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋']
variable {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋' V']

structure DegeneracyDescent (cd : CornerData (𝒪 := 𝒪) 𝕋 V)
    (cd' : CornerData (𝒪 := 𝒪) 𝕋' V') (n : ℕ) : Type where
  iRaw : Fin n → V →ₗ[𝒪] V'
  jRaw : Fin n → V' →ₗ[𝒪] V
  corner_i : ∀ (k : Fin n) (v : V), v ∈ cornerSubmodule (M := V) (cd.split.e cd.idx) →
    iRaw k v ∈ cornerSubmodule (M := V') (cd'.split.e cd'.idx)
  corner_j : ∀ (k : Fin n) (v' : V'), v' ∈ cornerSubmodule (M := V') (cd'.split.e cd'.idx) →
    jRaw k v' ∈ cornerSubmodule (M := V) (cd.split.e cd.idx)

namespace DegeneracyDescent

variable {cd : CornerData (𝒪 := 𝒪) 𝕋 V} {cd' : CornerData (𝒪 := 𝒪) 𝕋' V'} {n : ℕ}


end DegeneracyDescent

open CohCarrier in


end IharaTower
