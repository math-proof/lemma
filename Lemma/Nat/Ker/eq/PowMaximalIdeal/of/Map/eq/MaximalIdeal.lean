import Mathlib
import sympy.Basic


/--
[IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  {k : ℕ}
-- given
  (hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S) :
-- imply
  RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ k)).comp (algebraMap R S)) =
    IsLocalRing.maximalIdeal R ^ k := by
-- proof
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmax, ← Ideal.map_pow]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat _


-- created on 2026-10-03
