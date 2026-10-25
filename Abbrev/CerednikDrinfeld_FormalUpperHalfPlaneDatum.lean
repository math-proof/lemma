import Mathlib
import Structure.LatticeTreeOrbital
import Instance.CerednikDrinfeld_BruhatTitsTree
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

section Datum

variable (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)


variable {𝒪 K}


namespace DeligneDatum

variable {π}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

end DeligneDatum

abbrev OmegaObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type := DeligneDatum (K := K) π B

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

end Datum

section OmegaNr

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)

abbrev OmegaNrObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type :=
  (Onr →ₐ[𝒪] B) × OmegaObj (K := K) π B

end OmegaNr

end FormalOmega
end CerednikDrinfeld
