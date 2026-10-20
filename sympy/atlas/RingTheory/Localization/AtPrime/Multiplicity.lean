/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/AtPrime/Multiplicity.lean -/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Ideal multiplicity is unchanged under localization at a maximal ideal

For a Dedekind domain `R` and a maximal ideal `p`, the exponent of `p` in an
ideal `I` (as recorded by `emultiplicity`) agrees with the exponent of the
maximal ideal of any localization `Rₚ` at `p` in the mapped ideal `I.map`.

This invariant is the first corrected prerequisite for ATLAS `NumberTheoryI`
N261: the helper `different_valuation_exact` (claiming
`d_P = e_P - 1 + v_P(e_P)`) is false in wildly ramified extensions, so N261
will formalize only the true two-sided bound. Transporting valuations of
`differentIdeal A B` and of the correction term `Ideal.span {(e : B)}` to the
localization at a prime is the step that makes the local computation available.

## Main result

- `IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq`: the exponent of
  an ideal at a maximal ideal equals the exponent of its image at the maximal
  ideal of the localization.
-/

namespace IsLocalization.AtPrime

/-- The exponent of an ideal at a maximal ideal is unchanged by mapping to a
localization at that maximal ideal. -/
theorem emultiplicity_maximalIdeal_map_eq
    {R Rₚ : Type*} [CommRing R] [IsDedekindDomain R]
    (p : Ideal R) [p.IsMaximal] [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (I : Ideal R) :
    emultiplicity (IsLocalRing.maximalIdeal Rₚ)
        (I.map (algebraMap R Rₚ)) =
      emultiplicity p I := by
  have : IsDomain Rₚ := IsLocalization.isDomain_of_atPrime Rₚ p
  have : IsDedekindDomain Rₚ :=
    IsLocalization.AtPrime.isDedekindDomain R p Rₚ
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap, ← Ideal.under_def,
    IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ n]

end IsLocalization.AtPrime
