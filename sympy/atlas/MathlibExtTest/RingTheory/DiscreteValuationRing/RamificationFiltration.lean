/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/RamificationFiltration.lean -/


import sympy.atlas.RingTheory.DiscreteValuationRing.RamificationFiltration
import Lemma.Int.DiscreteValuationRing.RamificationFiltration

/-!
# Tests for the DVR ramification-power identity

Focused generic examples for
`IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx` and its
membership corollary, plus an identity-extension smoke test.
-/

open IsLocalRing

section GenericExamples

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]

/-- Generic example: the ideal identity applies to any torsion-free local DVR extension. -/
example : Ideal.map (algebraMap A B) (maximalIdeal A) =
    maximalIdeal B ^ (maximalIdeal B).ramificationIdx A :=
  IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx

/-- Generic example: the membership corollary applies to any element of the base
maximal ideal. -/
example {x : A} (hx : x ∈ maximalIdeal A) :
    algebraMap A B x ∈ maximalIdeal B ^ (maximalIdeal B).ramificationIdx A :=
  IsDiscreteValuationRing.algebraMap_mem_maximalIdeal_pow_ramificationIdx hx

end GenericExamples

section IdentityExtension

/-- Identity-extension smoke test: with the canonical self-algebra, the identity map
of a DVR is a torsion-free local homomorphism, so the ramification-power identity
applies to it. -/
example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ideal.map (algebraMap R R) (maximalIdeal R) =
      maximalIdeal R ^ (maximalIdeal R).ramificationIdx R :=
  IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx

end IdentityExtension
