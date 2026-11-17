module

public import Mathlib
public import Structure.WeierstrassCurve_ProjModel
public import Structure.WeierstrassCurve_DrinfeldBasisGlobal

set_option autoImplicit false

universe u

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

abbrev cls {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (p : MvPolynomial (Fin 3) T) :
    ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal p

end WeierstrassCurve.DrinfeldGlobal

end
