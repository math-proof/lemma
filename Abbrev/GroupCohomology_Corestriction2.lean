import Mathlib
import Structure.GroupCohomology_Corestriction2

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology
namespace Cores

section Transversal
variable {G : Type} [Group G] (H : Subgroup G)


namespace Transversal
variable {H}

abbrev qinv (x : G) : G ⧸ H := ((x⁻¹ : G) : G ⧸ H)

end Transversal

end Transversal

section Cor
variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

end Cor
end Cores

end groupCohomology
