import Mathlib
import Structure.WeierstrassCurve_ProjModel
import Structure.WeierstrassCurve_DrinfeldBasisGlobal
import Abbrev.WeierstrassCurve_SectionAtOrigin

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev ZChartRing : Type u := Away (projModelGradingCR W) (coord W 2)

abbrev zChartι : Spec (CommRingCat.of (ZChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos

end WeierstrassCurve.DrinfeldGlobal

end
