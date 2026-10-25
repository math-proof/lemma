-- Carved from Lemma/Definitions/Def_ModularCurve_IgusaScheme.lean: instance decls only.
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Lemma.ModularCurve.X0
import Def.GaloisRep_Flat
import Abbrev.ModularCurve_IgusaScheme
import Lemma.ModularCurve.IgusaScheme

set_option autoImplicit false

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
