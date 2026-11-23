-- Carved from Lemma/Definitions/Def_AlgebraicCurve_TwoChartIntegralModel.lean: instance decls only.
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Lifts
public import Theorem.Scheme.TwoChartIntegralModel
public import Def.AlgebraicCurve_TwoChartIntegralModel
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace AlgebraicCurve

namespace TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

variable {R F j}

variable (R F j)

instance isOpenImmersion_fFin : IsOpenImmersion (fFin R F j) := by
  let := (inclFin R F j).toRingHom.toAlgebra
  have := isLocalization_away_inclFin R F j
  exact IsOpenImmersion.of_isLocalization (jChartFin R F j)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf R F j) := by
  let := (inclInf R F j).toRingHom.toAlgebra
  have := isLocalization_away_inclInf R F j
  exact IsOpenImmersion.of_isLocalization (jInvChartInf R F j)

instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin R F j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf R F j) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin R F j) (fInf R F j))).map_prop WalkingSpan.right


end TwoChartIntegralModel

end AlgebraicCurve

end
