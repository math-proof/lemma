/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/FiniteRamification.lean -/


import Lemma.Nat.NumberField.FiniteRamification

open IsDedekindDomain
open scoped NumberField

/-!
# Finite-ramification smoke tests

The two examples test the minimal no-Galois API
(`NumberField.finite_ramified_primes`) and the finite exceptional-set
consumer keeping native `Algebra.IsUnramifiedIn` outside it.
-/

/-- Direct consumption of the finite-ramification theorem. -/
example (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    {p : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal}.Finite :=
  NumberField.finite_ramified_primes K L

/-- Finite exceptional set outside which native `IsUnramifiedIn` holds. -/
example (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ s : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∀ p : HeightOneSpectrum (NumberField.RingOfIntegers K), p ∉ s →
        Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal := by
  classical
  refine ⟨(NumberField.finite_ramified_primes K L).toFinset, fun p hp => ?_⟩
  by_contra hcon
  exact hp ((Set.Finite.mem_toFinset _).mpr hcon)
