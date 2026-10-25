import Mathlib
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CerednikDrinfeld.FormalOmega

variable {𝒪 : Type} [CommRing 𝒪]

abbrev Scheme.specOver (B : Type) [CommRing B] [Algebra 𝒪 B] : Spec (.of B) ⟶ Spec (.of 𝒪) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))

end AlgebraicGeometry

end
