import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Localization.AtPrime.Multiplicity
open IsLocalization.AtPrime


/--
[emultiplicity_maximalIdeal_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/AtPrime/Multiplicity.lean)
-/
@[path]
private lemma emultiplicity_maximalIdeal_map_eq_eq
  [CommRing R] [IsDedekindDomain R] [CommRing Rₚ] [Algebra R Rₚ] [IsLocalRing Rₚ]
  {p : Ideal R} [p.IsMaximal] [IsLocalization.AtPrime Rₚ p]
  {I : Ideal R} :
-- imply
  emultiplicity (IsLocalRing.maximalIdeal Rₚ)
        (I.map (algebraMap R Rₚ)) =
      emultiplicity p I := by
-- proof
  apply IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq p I


-- created on 2026-10-20
