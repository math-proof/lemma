/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/ElementDifferent.lean -/


import sympy.atlas.RingTheory.DedekindDomain.ElementDifferent
import Lemma.Int.DedekindDomain.ElementDifferent


/-!
# Tests for the element different

Generic branch-hypothesis examples exercising the primitive and nonprimitive
branches of `elementDifferent`, its zero characterization, and its membership
in `differentIdeal A B`, plus one concrete primitive computation over `ℤ/ℚ`,
and principal-different tests for `differentIdeal_eq_span_derivative_of_adjoin_eq_top`.
-/

set_option autoImplicit false

variable (A K L : Type*) {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A B] [Algebra B L] [Algebra K L]

/-- Primitive branch: the element different unfolds to the derivative evaluation. -/
example (α : B) (hα : Algebra.adjoin K {algebraMap B L α} = ⊤) :
    elementDifferent A K L α =
      Polynomial.aeval α (Polynomial.derivative (minpoly A α)) :=
  elementDifferent_of_adjoin_eq_top A K L α hα

/-- Nonprimitive branch: the element different vanishes. -/
example (α : B) (hα : Algebra.adjoin K {algebraMap B L α} ≠ ⊤) :
    elementDifferent A K L α = 0 :=
  elementDifferent_of_adjoin_ne_top A K L α hα

/-- The zero characterization applies as stated. -/
example (α : B) :
    elementDifferent A K L α = 0 ↔
      Algebra.adjoin K {algebraMap B L α} ≠ ⊤ ∨
        Polynomial.aeval α (Polynomial.derivative (minpoly A α)) = 0 :=
  elementDifferent_eq_zero_iff A K L α

/-- Membership in the different ideal in the primitive case. -/
example [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B]
    (α : B) (hα : Algebra.adjoin K {algebraMap B L α} = ⊤) :
    elementDifferent A K L α ∈ differentIdeal A B :=
  elementDifferent_mem_differentIdeal A K L α hα

/-- Over `ℚ/ℚ`, every element is primitive, so the element different of
`q : ℚ` over `ℤ` unfolds to the derivative evaluation. -/
example (q : ℚ) : Algebra.adjoin ℚ {algebraMap ℚ ℚ q} = ⊤ := by
  rw [Algebra.eq_top_iff]
  intro y
  have h : algebraMap ℚ ℚ y ∈ Algebra.adjoin ℚ {algebraMap ℚ ℚ q} :=
    (Algebra.adjoin ℚ {algebraMap ℚ ℚ q}).algebraMap_mem y
  rwa [Algebra.algebraMap_self_apply] at h

example (q : ℚ) (hα : Algebra.adjoin ℚ {algebraMap ℚ ℚ q} = ⊤) :
    elementDifferent ℤ ℚ ℚ q =
      Polynomial.aeval q (Polynomial.derivative (minpoly ℤ q)) :=
  elementDifferent_of_adjoin_eq_top ℤ ℚ ℚ q hα

/-- The different is principal from the ring-generation hypothesis alone,
with no separate field-generation hypothesis. -/
example [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B]
    (α : B) (hα : Algebra.adjoin A {α} = ⊤) :
    differentIdeal A B =
      Ideal.span {Polynomial.aeval α (Polynomial.derivative (minpoly A α))} :=
  differentIdeal_eq_span_derivative_of_adjoin_eq_top A K L α hα

/-- The principal-different equality at a power-basis generator. -/
example [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B]
    (pb : PowerBasis A B) :
    differentIdeal A B =
      Ideal.span
        {Polynomial.aeval pb.gen (Polynomial.derivative (minpoly A pb.gen))} :=
  differentIdeal_eq_span_derivative_of_adjoin_eq_top A K L pb.gen
    pb.adjoin_gen_eq_top
