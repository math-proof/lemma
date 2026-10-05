import Mathlib
import sympy.Basic


/--
[Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsDomain R]
  {p : Ideal R} [p.IsPrime]
-- given
  (h : IsDiscreteValuationRing (Localization.AtPrime p)) :
-- imply
  p.height = 1 := by
-- proof
  have := h
  have hnf : ¬ IsField (Localization.AtPrime p) := fun hF =>
    IsDiscreteValuationRing.not_a_field (R := Localization.AtPrime p)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have hd1 : ringKrullDim (Localization.AtPrime p) = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one (Localization.AtPrime p) hnf
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)] at hd1
  exact_mod_cast hd1


-- created on 2026-10-03
