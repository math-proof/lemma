import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.RamificationFiltration
open IsLocalRing
open IsDiscreteValuationRing


namespace IsDiscreteValuationRing

/--
[map_maximalIdeal_eq_pow_ramificationIdx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/RamificationFiltration.lean)
-/
@[path]
lemma map_maximalIdeal_eq_pow_ramificationIdx
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)] :
-- imply
  Ideal.map (algebraMap A B) (maximalIdeal A) =
    maximalIdeal B ^ (maximalIdeal B).ramificationIdx A := by
-- proof
  have hA0 : maximalIdeal A ≠ ⊥ := not_a_field A
  have hB0 : maximalIdeal B ≠ ⊥ := not_a_field B
  have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hA0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible B
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hmap hϖ
  have hspan : Ideal.span ({ϖ ^ n} : Set B) = maximalIdeal B ^ n := by
    rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have hBunit : ¬ IsUnit (maximalIdeal B) :=
    (Ideal.prime_of_isPrime hB0 inferInstance).not_isUnit
  have he : (maximalIdeal B).ramificationIdx A =
    multiplicity (maximalIdeal B) (Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hmap
  have hmult : multiplicity (maximalIdeal B)
    (Ideal.map (algebraMap A B) (maximalIdeal A)) = n := by
    rw [hn, hspan]
    exact multiplicity_pow_self hB0 hBunit n
  calc Ideal.map (algebraMap A B) (maximalIdeal A)
    = maximalIdeal B ^ n := by rw [hn, hspan]
    _ = maximalIdeal B ^ (maximalIdeal B).ramificationIdx A := by rw [he, hmult]

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/--
[algebraMap_mem_maximalIdeal_pow_ramificationIdx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/RamificationFiltration.lean)
-/
@[path]
lemma algebraMap_mem_maximalIdeal_pow_ramificationIdx
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]
  {x : A}
-- given
  (hx : x ∈ maximalIdeal A) :
-- imply
  algebraMap A B x ∈ maximalIdeal B ^ (maximalIdeal B).ramificationIdx A := by
-- proof
  rw [← map_maximalIdeal_eq_pow_ramificationIdx]
  exact Ideal.mem_map_of_mem _ hx

end IsDiscreteValuationRing


-- created on 2026-10-20
-- updated on 2026-10-23
