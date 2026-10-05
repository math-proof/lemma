import Mathlib
import sympy.Basic


/--
[Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {x : R}
  {P : Ideal R} [P.IsPrime]
-- given
  (hx : x ≠ 0)
  (hxP : x ∈ P) :
-- imply
  P.height = 1 ↔ P ∈ (Ideal.span {x}).minimalPrimes := by
-- proof
  have hle : Ideal.span {x} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hxP
  have hx' : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  have hxu : ¬ IsUnit x := fun hu => Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem P hxP hu)
  have hspan : (Ideal.span {x}).height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hx' hxu
  constructor
  · intro hP
    exact Ideal.mem_minimalPrimes_of_height_eq hle (by rw [hP, hspan])
  · intro hP
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) P hP
    · exact hspan ▸ Ideal.height_mono hle


-- created on 2026-10-05
