import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.TameDifferent
open IsLocalRing
open scoped nonZeroDivisors


/--
[differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/TameDifferent.lean)
-/
@[path]
private lemma differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {e : ℕ}
-- given
  (heUnit : IsUnit (e : B))
  (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) :
-- imply
  differentIdeal A B = maximalIdeal B ^ (e - 1) := by
-- proof
  apply differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast A B e heUnit he


-- created on 2026-10-20
