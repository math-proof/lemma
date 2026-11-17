module

public import Mathlib
public import Structure.WeierstrassCurve_ProjModel
public import Structure.WeierstrassCurve_DrinfeldBasisGlobal

set_option autoImplicit false

universe u

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev coord (i : Fin 3) : ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)

abbrev OriginChartRing : Type u := Away (projModelGradingCR W) (coord W 1)

end WeierstrassCurve.DrinfeldGlobal

end
