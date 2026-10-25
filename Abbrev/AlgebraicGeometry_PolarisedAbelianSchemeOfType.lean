import Structure.AlgebraicGeometry_FramedPolarisedAbelianScheme
import Def.AlgebraicGeometry_PolarisationRosati
import Structure.AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace Scheme.Modules

end Scheme.Modules

namespace Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

end Polarisation

namespace PolarisedAbelianScheme

abbrev typeGroup {g : ℕ} (δ : Fin g → ℕ) : Type := ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))

variable {g d n : ℕ}


namespace Satisfying

variable {Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop}


end Satisfying

end PolarisedAbelianScheme

end AlgebraicGeometry

end
