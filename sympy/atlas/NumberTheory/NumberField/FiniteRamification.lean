/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/FiniteRamification.lean -/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finitely many ramified primes

This file is a clean prerequisite for ATLAS `NumberTheoryI` target N438.

Source-to-API mapping: frozen ATLAS declaration
`GlobalConductor.finite_ramified_primes`,
[`v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean` lines 171--215 at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean#L171-L215).

This replaces `GlobalCFT.IsUnramifiedIn` by native `Algebra.IsUnramifiedIn`,
drops ATLAS's unused Galois/explicit finite-dimension hypotheses, and is only
a clean N438 prerequisite. It does not establish local conductor existence,
unramified exponent zero, conductor finite support, or `conductorModulus`.
-/

open IsDedekindDomain

namespace NumberField

/-- Only finitely many height-one primes of a number field ramify
in a number-field extension. -/
theorem finite_ramified_primes
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    {p : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal}.Finite := by
  classical
  let _ : Algebra
      (FractionRing (NumberField.RingOfIntegers K))
      (FractionRing (NumberField.RingOfIntegers L)) :=
    FractionRing.liftAlgebra _ _
  let f := fun P : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
    P.under (NumberField.RingOfIntegers K)
  have hfinite : {P : HeightOneSpectrum (NumberField.RingOfIntegers L) |
      P.asIdeal ∣ differentIdeal (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  apply (hfinite.image f).subset
  intro p hp
  rw [Set.mem_image]
  change ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal at hp
  simp only [Algebra.IsUnramifiedIn, not_forall] at hp
  obtain ⟨P, hPprime, hPover, hPram⟩ := hp
  let _ : P.IsPrime := hPprime
  let _ : P.LiesOver p.asIdeal := hPover
  let Q : HeightOneSpectrum (NumberField.RingOfIntegers L) :=
    ⟨P, hPprime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  refine ⟨Q, ?_, ?_⟩
  · exact (dvd_differentIdeal_iff
      (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers L)).2 hPram
  · apply HeightOneSpectrum.ext
    exact Ideal.LiesOver.over.symm

end NumberField
