import Instance.AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra
import Def.AlgebraicGeometry_ProjectiveWeierstrassPolynomialPrime
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Structure.WeierstrassCurve_ProjModel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassProjModel

end WeierstrassProjModel

namespace WeierstrassProjModel

open NeronModelInfra


namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

end RelativeGroupLaw

end WeierstrassProjModel
end

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩

end RelativeGroupLaw

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open NeronModelInfra

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

section Carrier

variable {R : Type*} [CommRing R]

end Carrier

section PointsEval

variable {R : Type u} [CommRing R]

end PointsEval

end WeierstrassProjModel

end
