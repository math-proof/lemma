import Mathlib
import Structure.WeierstrassCurve_ProjModel
import Structure.WeierstrassCurve_DrinfeldBasisGlobal

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

abbrev cls {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (p : MvPolynomial (Fin 3) T) :
    ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal p

end WeierstrassCurve.DrinfeldGlobal

end
