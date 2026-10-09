import Mathlib
import sympy.Basic


/--
[HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {R' : Type u} [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  {H' : Type v} [CommRing H'] [HopfAlgebra R H']
  {φ : H →ₐc[R] H'}
-- given
  (hφ : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R')) :
-- imply
  Function.Bijective φ := by
-- proof
  have h : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.lTensor R') := by
    rwa [← LinearMap.baseChange_eq_ltensor]
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R R' _).mp h


-- created on 2026-10-03
