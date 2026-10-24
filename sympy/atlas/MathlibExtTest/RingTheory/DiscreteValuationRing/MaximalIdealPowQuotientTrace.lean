/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean -/

/-
Author: Muse Code
-/

import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace
import Lemma.Int.DiscreteValuationRing.MaximalIdealPowQuotientTrace

/-!
# Tests for the maximal-ideal-power quotient trace formulas

These examples exercise the public API of
`MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace`:
the one-step trace recurrence `trace_residueFieldMaximalIdealPowQuotient_succ`,
the iterated quotient trace formula
`trace_residueFieldMaximalIdealPowQuotient`, the integral-trace residue bridge
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`, the tame
trace-surjectivity theorem
`intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow`, and the
`n = 0` and `n = 1` sanity specializations.
-/


open IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]

/-- The one-step trace recurrence applies as stated. -/
example (n : ℕ)
    (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ (n + 1))
    [IsLocalHom (algebraMap A B)]
    [Module (ResidueField A)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [IsScalarTower (ResidueField A) (ResidueField B)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B (n + 1))]
    (b : B) :
    Algebra.trace (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b) =
      Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B b) +
        Algebra.trace (ResidueField A)
          (ResidueFieldMaximalIdealPowQuotient A B n)
          (Ideal.Quotient.mk _ b) :=
  trace_residueFieldMaximalIdealPowQuotient_succ A B n hSucc b

/-- The iterated quotient trace formula applies as stated. -/
example (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n)
    [IsLocalHom (algebraMap A B)]
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B n)]
    (b : B) :
    Algebra.trace (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B n)
        (Ideal.Quotient.mk _ b) =
      n • Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B b) :=
  trace_residueFieldMaximalIdealPowQuotient A B n h b

/-- The integral-trace residue bridge applies as stated: under
`map 𝔪A = 𝔪B ^ e`, the residue of the integral trace is `e` times the
residue-field trace. This is a congruence modulo `maximalIdeal A` only. -/
example (e : ℕ)
    [Module.IsTorsionFree A B] [Module.Finite A B]
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) =
      maximalIdeal B ^ e)
    (b : B) :
    IsLocalRing.residue A (Algebra.intTrace A B b) =
      e • Algebra.trace (ResidueField A)
        (ResidueField B) (IsLocalRing.residue B b) :=
  residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow A B e he b

/-- Sanity check at index zero: the quotient is trivial, so the trace is zero. -/
example
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ 0)
    [IsLocalHom (algebraMap A B)]
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B 0)]
    (b : B) :
    Algebra.trace (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B 0)
        (Ideal.Quotient.mk _ b) = 0 := by
  have h0 := trace_residueFieldMaximalIdealPowQuotient A B 0 h b
  simpa using h0

/-- Sanity check at index one: the trace is the residue-field trace. -/
example
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ 1)
    [IsLocalHom (algebraMap A B)]
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B 1)]
    (b : B) :
    Algebra.trace (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B 1)
        (Ideal.Quotient.mk _ b) =
      Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B b) := by
  have h1 := trace_residueFieldMaximalIdealPowQuotient A B 1 h b
  simpa using h1

/-- The tame integral-trace surjectivity applies as stated: under
`map 𝔪A = 𝔪B ^ e` with `IsUnit (e : B)`, the integral trace is surjective.
This exercises only the tame trace-surjectivity input, not the
mixed-characteristic wild bound or ATLAS's false exact wild equality. -/
example (e : ℕ)
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (heUnit : IsUnit (e : B))
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) =
      maximalIdeal B ^ e) :
    Function.Surjective (Algebra.intTrace A B) :=
  intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow A B e
    heUnit he
