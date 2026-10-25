-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings.lean: instance decls only.
import Mathlib
import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Lemma.CerednikDrinfeld.FormalUpperHalfPlaneChartRings

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CerednikDrinfeld
namespace FormalOmega

section ChartRings

variable (R : Type) [CommRing R]


instance edgeQuot.instCommRing (π : R) : CommRing (edgeQuot R π) :=
  show CommRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}) from inferInstance

instance edgeQuot.instAlgebra (π : R) : Algebra R (edgeQuot R π) :=
  show Algebra R (MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}) from inferInstance


end ChartRings

end FormalOmega
end CerednikDrinfeld

end
