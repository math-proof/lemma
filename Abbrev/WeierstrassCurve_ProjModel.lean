module
public import Instance.AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra
public import Def.AlgebraicGeometry_ProjectiveWeierstrassPolynomialPrime
public import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Structure.WeierstrassCurve_ProjModel
set_option autoImplicit false


public section

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
