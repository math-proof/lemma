import Mathlib
import Initialize.Tactic.Attr.Basic


namespace IsLocalization.AtPrime

/--
[emultiplicity_maximalIdeal_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/AtPrime/Multiplicity.lean)
-/
@[path]
lemma emultiplicity_maximalIdeal_map_eq
  [CommRing R] [IsDedekindDomain R] [CommRing Rₚ] [Algebra R Rₚ] [IsLocalRing Rₚ]
  {p : Ideal R} [p.IsMaximal] [IsLocalization.AtPrime Rₚ p]
  {I : Ideal R} :
-- imply
  emultiplicity (IsLocalRing.maximalIdeal Rₚ)
    (I.map (algebraMap R Rₚ)) =
    emultiplicity p I := by
-- proof
  have : IsDomain Rₚ := IsLocalization.isDomain_of_atPrime Rₚ p
  have : IsDedekindDomain Rₚ :=
    IsLocalization.AtPrime.isDedekindDomain R p Rₚ
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap, ← Ideal.under_def,
    IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ n]

end IsLocalization.AtPrime


-- created on 2026-10-20
-- updated on 2026-10-26
