import Mathlib
import Structure.CerednikDrinfeld_FormalUpperHalfPlanePoints
import Structure.CerednikDrinfeld_DrinfeldQuadruple

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct

namespace CerednikDrinfeld
namespace FormalOmega

section DetIndex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]


end DetIndex

section Datum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]


abbrev toLocRing (x : PrimeSpectrum B) : B →ₐ[𝒪] locRing B x :=
  IsScalarTower.toAlgHom 𝒪 B (locRing B x)


variable {B}


namespace DrinfeldDatum

variable {π}

abbrev L₀ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Q.N₀ x, Q.full₀ x⟩

abbrev L₁ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Q.N₁ x, Q.full₁ x⟩


end DrinfeldDatum

end Datum

end FormalOmega
end CerednikDrinfeld

end
