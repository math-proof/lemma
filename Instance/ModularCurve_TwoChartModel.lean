-- Carved from Lemma/Definitions/Def_ModularCurve_TwoChartModel.lean: instance decls only.
import Mathlib
import Abbrev.ModularCurve_TwoChartModel

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace ModularCurve

namespace TwoChart

variable (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K]

variable {A K}

variable (A K)

variable (j : K) [Fact (j ≠ 0)]

instance isOpenImmersion_fFin : IsOpenImmersion (fFin A K j) := by
  let := (inclFin A K j).toRingHom.toAlgebra
  have := isLocalization_away_inclFin A K j
  exact IsOpenImmersion.of_isLocalization (jChartFin A K j)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf A K j) := by
  let := (inclInf A K j).toRingHom.toAlgebra
  have := isLocalization_away_inclInf A K j
  exact IsOpenImmersion.of_isLocalization (jInvChartInf A K j)

instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin A K j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin A K j) (fInf A K j))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf A K j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin A K j) (fInf A K j))).map_prop WalkingSpan.right

end TwoChart

end ModularCurve

end
