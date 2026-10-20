import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.RamificationInertia.Valuation
open IsDiscreteValuationRing


/--
[emultiplicity_maximalIdeal_span_eq_addVal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RamificationInertia/Valuation.lean)
-/
@[path]
private lemma emultiplicity_maximalIdeal_span_eq_addVal_eq
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {x : R} :
-- imply
  emultiplicity (IsLocalRing.maximalIdeal R) (Ideal.span {x}) = addVal R x := by
-- proof
  apply IsDiscreteValuationRing.emultiplicity_maximalIdeal_span_eq_addVal x

/--
[IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RamificationInertia/Valuation.lean)
-/
@[path]
private lemma IsDiscreteValuationRing_addVal_algebraMap_eq_ramificationIdx_mul_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]
  {x : A} :
-- imply
  addVal B (algebraMap A B x) =
    ((IsLocalRing.maximalIdeal B).ramificationIdx A : ℕ∞) * addVal A x := by
-- proof
  apply IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul x

/--
[IsLocalRing.isUnit_natCast_iff_ringChar_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/RamificationInertia/Valuation.lean)
-/
@[path]
private lemma IsLocalRing_isUnit_natCast_iff_ringChar_not_dvd_eq
  [CommRing R] [IsLocalRing R]
  {n : ℕ} :
-- imply
  IsUnit (n : R) ↔ ¬ ringChar (IsLocalRing.ResidueField R) ∣ n := by
-- proof
  apply IsLocalRing.isUnit_natCast_iff_ringChar_not_dvd n


-- created on 2026-10-20
