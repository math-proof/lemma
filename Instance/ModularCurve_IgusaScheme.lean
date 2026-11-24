module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Lifts
public import Theorem.HahnSeries.X0
public import Def.GaloisRep_Flat
public import Abbrev.ModularCurve_IgusaScheme
public import Theorem.Scheme.IgusaScheme
public import Def.ModularCurve_IgusaScheme
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_IgusaScheme.lean: instance decls only.

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace ModularCurve

namespace IgusaScheme

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

instance fact_jFull_ne_zero : Fact (jFull N ≠ 0) := ⟨jFull_ne_zero N⟩

variable {N ℓ}

variable (N ℓ)

instance isOpenImmersion_fFin : IsOpenImmersion (fFin N ℓ) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact IsOpenImmersion.of_isLocalization (jChartFin N ℓ)

instance isOpenImmersion_fInf : IsOpenImmersion (fInf N ℓ) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact IsOpenImmersion.of_isLocalization (jInvChartInf N ℓ)

instance isOpenImmersion_ιFin : IsOpenImmersion (ιFin N ℓ) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).map_prop WalkingSpan.left

instance isOpenImmersion_ιInf : IsOpenImmersion (ιInf N ℓ) :=
  (Scheme.IsLocallyDirected.openCover (span (fFin N ℓ) (fInf N ℓ))).map_prop WalkingSpan.right

end IgusaScheme

end ModularCurve

end
