import Mathlib
import sympy.Basic
import sympy.functions.special.elliptic.ComplexMultiplication


/--
[ComplexMultiplication](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/ComplexMultiplication.lean)
-/
@[path]
private lemma mem_endomorphism_ring_iff
-- given
  (L : PeriodPair)
  (a : ℂ) :
-- imply
  a ∈ L.endomorphismRing ↔ ∀ z ∈ L.lattice, a * z ∈ L.lattice := by
-- proof
  apply PeriodPair.mem_endomorphismRing

/--
[ComplexMultiplication](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/ComplexMultiplication.lean)
-/
@[path]
private lemma is_proper_ideal_endomorphism_ring_is
-- given
  (L : PeriodPair) :
-- imply
  L.IsProperIdeal L.endomorphismRing := by
-- proof
  apply PeriodPair.isProperIdeal_endomorphismRing L


-- created on 2026-10-11
