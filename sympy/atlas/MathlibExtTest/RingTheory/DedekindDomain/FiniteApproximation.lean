/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/FiniteApproximation.lean -/

/-
Author: Muse Code
-/

import Lemma.Int.DedekindDomain.FiniteApproximation

/-!
# Tests for finite approximation at height-one primes

Generic API checks for `Ideal.exists_elem_eq_valuation_at_primes` and
`FractionalIdeal.exists_elem_eq_valuation_at_primes`: full call,
empty-finset specialization, and singleton specialization for each
(three integral and three fractional generic tests).
-/


open UniqueFactorizationMonoid IsDedekindDomain Ideal Finset

open scoped nonZeroDivisors

namespace MathlibExtTest.RingTheory.DedekindDomain.FiniteApproximation

/-- Generic call to `Ideal.exists_elem_eq_valuation_at_primes`. -/
example {A : Type*} [CommRing A] [IsDedekindDomain A]
    {ι : Type*} (s : Finset ι) (ps : ι → HeightOneSpectrum A)
    (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ (0 : A) ∧
      ∀ i ∈ s,
        let e := Multiset.count (normalize (ps i).asIdeal) (normalizedFactors I)
        x ∈ (ps i).asIdeal ^ e ∧ x ∉ (ps i).asIdeal ^ (e + 1) :=
  Ideal.exists_elem_eq_valuation_at_primes s ps I hI

/-- Empty-finset specialization: extract `x ∈ I` and `x ≠ 0`. -/
example {A : Type*} [CommRing A] [IsDedekindDomain A]
    (ps : Empty → HeightOneSpectrum A)
    (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ (0 : A) := by
  obtain ⟨x, hx, hx_ne, _⟩ :=
    Ideal.exists_elem_eq_valuation_at_primes (∅ : Finset Empty) ps I hI
  exact ⟨x, hx, hx_ne⟩

/-- Singleton specialization: exact normalized-factor power membership and
nonmembership in the next power. -/
example {A : Type*} [CommRing A] [IsDedekindDomain A]
    (p : HeightOneSpectrum A)
    (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ (0 : A) ∧
      (let e := Multiset.count (normalize p.asIdeal) (normalizedFactors I)
      x ∈ p.asIdeal ^ e ∧ x ∉ p.asIdeal ^ (e + 1)) := by
  obtain ⟨x, hx, hx_ne, hval⟩ :=
    Ideal.exists_elem_eq_valuation_at_primes ({()} : Finset Unit) (fun _ => p) I hI
  exact ⟨x, hx, hx_ne, hval () (Finset.mem_singleton_self ())⟩

/-- Generic call to `FractionalIdeal.exists_elem_eq_valuation_at_primes`. -/
example {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {ι : Type*} (s : Finset ι) (ps : ι → HeightOneSpectrum A)
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ∃ x ∈ I, x ≠ (0 : K) ∧
      ∀ i ∈ s,
        FractionalIdeal.count K (ps i) (FractionalIdeal.spanSingleton A⁰ x) =
          FractionalIdeal.count K (ps i) I :=
  FractionalIdeal.exists_elem_eq_valuation_at_primes s ps I hI

/-- Empty-finset specialization: extract a nonzero member of a fractional ideal. -/
example {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (ps : Empty → HeightOneSpectrum A)
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ∃ x ∈ I, x ≠ (0 : K) := by
  obtain ⟨x, hx, hx_ne, _⟩ :=
    FractionalIdeal.exists_elem_eq_valuation_at_primes (∅ : Finset Empty) ps I hI
  exact ⟨x, hx, hx_ne⟩

/-- Singleton specialization: exact fractional-count equality at one prime. -/
example {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : HeightOneSpectrum A)
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ∃ x ∈ I, x ≠ (0 : K) ∧
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton A⁰ x) =
        FractionalIdeal.count K p I := by
  obtain ⟨x, hx, hx_ne, hval⟩ :=
    FractionalIdeal.exists_elem_eq_valuation_at_primes ({()} : Finset Unit)
      (fun _ => p) I hI
  exact ⟨x, hx, hx_ne, hval () (Finset.mem_singleton_self ())⟩

end MathlibExtTest.RingTheory.DedekindDomain.FiniteApproximation
