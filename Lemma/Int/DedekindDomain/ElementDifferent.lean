import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.ElementDifferent


/--
[elementDifferent_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
private lemma elementDifferent_of_adjoin_eq_top_eq
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L]
  {α : B}
-- given
  (hα : Algebra.adjoin K {algebraMap B L α} = ⊤) :
-- imply
  elementDifferent A K L α =
    Polynomial.aeval α (Polynomial.derivative (minpoly A α)) := by
-- proof
  apply elementDifferent_of_adjoin_eq_top A K L α hα

/--
[elementDifferent_of_adjoin_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
private lemma elementDifferent_of_adjoin_ne_top_eq
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L]
  {α : B}
-- given
  (hα : Algebra.adjoin K {algebraMap B L α} ≠ ⊤) :
-- imply
  elementDifferent A K L α = 0 := by
-- proof
  apply elementDifferent_of_adjoin_ne_top A K L α hα

/--
[elementDifferent_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
private lemma elementDifferent_eq_zero_iff_eq
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L]
  {α : B} :
-- imply
  elementDifferent A K L α = 0 ↔
    Algebra.adjoin K {algebraMap B L α} ≠ ⊤ ∨
    Polynomial.aeval α (Polynomial.derivative (minpoly A α)) = 0 := by
-- proof
  apply elementDifferent_eq_zero_iff A K L α

/--
[elementDifferent_mem_differentIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
private lemma elementDifferent_mem_differentIdeal_eq
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  {α : B}
-- given
  (hα : Algebra.adjoin K {algebraMap B L α} = ⊤) :
-- imply
  elementDifferent A K L α ∈ differentIdeal A B := by
-- proof
  apply elementDifferent_mem_differentIdeal A K L α hα

/--
[differentIdeal_eq_span_derivative_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
private lemma differentIdeal_eq_span_derivative_of_adjoin_eq_top_eq
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  {α : B}
-- given
  (hα : Algebra.adjoin A {α} = ⊤) :
-- imply
  differentIdeal A B =
    Ideal.span {Polynomial.aeval α (Polynomial.derivative (minpoly A α))} := by
-- proof
  apply differentIdeal_eq_span_derivative_of_adjoin_eq_top A K L α hα


-- created on 2026-10-20
