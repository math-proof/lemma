import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.FiniteApproximation
open UniqueFactorizationMonoid IsDedekindDomain Ideal Finset
open scoped nonZeroDivisors


/--
[Ideal.exists_elem_eq_valuation_at_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FiniteApproximation.lean)
-/
@[path]
private lemma Ideal_exists_elem_eq_valuation_at_primes_eq
  [CommRing A] [IsDedekindDomain A]
  {s : Finset ι}
  {ps : ι → HeightOneSpectrum A}
  {I : Ideal A}
-- given
  (hI : I ≠ ⊥) :
-- imply
  ∃ x ∈ I, x ≠ (0 : A) ∧
    ∀ i ∈ s,
    let e := by
-- proof
  apply Ideal.exists_elem_eq_valuation_at_primes s ps I hI

/--
[FractionalIdeal.exists_elem_eq_valuation_at_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FiniteApproximation.lean)
-/
@[path]
private lemma FractionalIdeal_exists_elem_eq_valuation_at_primes_eq
  [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {s : Finset ι}
  {ps : ι → HeightOneSpectrum A}
  {I : FractionalIdeal A⁰ K}
-- given
  (hI : I ≠ 0) :
-- imply
  ∃ x ∈ I, x ≠ (0 : K) ∧
    ∀ i ∈ s,
    FractionalIdeal.count K (ps i) (FractionalIdeal.spanSingleton A⁰ x) =
    FractionalIdeal.count K (ps i) I := by
-- proof
  apply FractionalIdeal.exists_elem_eq_valuation_at_primes s ps I hI


-- created on 2026-10-20
