import Mathlib
import Structure.AlgebraicGeometry_TwoAffineOpenCover
import Structure.AlgebraicGeometry_TwoChartCechLaurentChart
import Structure.AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option autoImplicit false

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))


variable {𝒱 c}


abbrev sectionResidue {ι : Type v} (Λ : ι → (𝒱.cover c).LaurentChart) (i : ι) :
    Ω[(𝒱.cover c).A01⁄R] →ₗ[R] R :=
  (Λ i).residue

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
