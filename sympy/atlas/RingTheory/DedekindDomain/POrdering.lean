/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/POrdering.lean -/

import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Bhargava p-ordering of an infinite subset of a Dedekind domain

This module formalizes the p-ordering definition from the Introduction,
lines 52-60, of Wataru Takeda, On the Bhargava factorial of polynomial
maps, arXiv:2304.02946v1. The source index slip is read as stage `n`.
-/

namespace IsDedekindDomain.HeightOneSpectrum

/-- Additive valuation of the prefix product at stage `n` for candidate `x`:
`emultiplicity` of the height-one prime in the principal ideal spanned by
`∏ k in range n, (x - a k)`. Source: Takeda, Introduction, lines 52-60. -/
noncomputable def pOrderingValuation
    {R : Type*} [CommRing R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : ℕ → R) (n : ℕ)
    (x : R) : ℕ∞ :=
  emultiplicity p.asIdeal
    (Ideal.span {(Finset.range n).prod fun k => x - a k})

/-- Bhargava p-ordering of the infinite subset `S` of the Dedekind domain:
every term of `a` lies in `S`, and each term attains the minimum
prefix-product valuation over `S`.
Source: Takeda, Introduction, lines 52-60. -/
def IsPOrdering
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (S : Set R)
    (a : ℕ → R) : Prop :=
  S.Infinite ∧ (∀ n, a n ∈ S) ∧
    ∀ n, ∀ x ∈ S,
      pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x

/-- Unfolding characterization of `IsPOrdering`. -/
theorem isPOrdering_unfold
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} :
    IsPOrdering p S a ↔
      S.Infinite ∧ (∀ n, a n ∈ S) ∧
        ∀ n, ∀ x ∈ S,
          pOrderingValuation p a n (a n) ≤
            pOrderingValuation p a n x :=
  Iff.rfl

/-- Accessor: the underlying set is infinite. -/
theorem IsPOrdering.infinite
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) : S.Infinite :=
  h.1

/-- Accessor: every sequence term lies in `S`. -/
theorem IsPOrdering.mem
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) (n : ℕ) : a n ∈ S :=
  h.2.1 n

/-- Accessor: the minimum property at every stage. -/
theorem IsPOrdering.min_le
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) (n : ℕ) (x : R)
    (hx : x ∈ S) :
    pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x :=
  h.2.2 n x hx

/-- The minimum property as an `IsLeast` statement. -/
theorem IsPOrdering.isLeast
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} {n : ℕ} (h : IsPOrdering p S a) :
    IsLeast (pOrderingValuation p a n '' S)
      (pOrderingValuation p a n (a n)) := by
  constructor
  · exact ⟨a n, h.mem n, rfl⟩
  · intro y hy
    obtain ⟨x, hxS, rfl⟩ := hy
    exact h.min_le n x hxS

/-- Constructor for `IsPOrdering` from its three components. -/
theorem IsPOrdering.intro
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (hinf : S.Infinite) (hmem : ∀ n, a n ∈ S)
    (hmin : ∀ n, ∀ x ∈ S,
      pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x) :
    IsPOrdering p S a :=
  ⟨hinf, hmem, hmin⟩

/-- At stage zero the product is empty, so the valuation is zero. -/
theorem pOrderingValuation_zero
    {R : Type*} [CommRing R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : ℕ → R)
    (x : R) : pOrderingValuation p a 0 x = 0 := by
  unfold pOrderingValuation
  rw [Finset.range_zero, Finset.prod_empty,
    Ideal.span_singleton_one]
  have hunit : ¬ IsUnit p.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact p.isPrime.ne_top
  have htop : (⊤ : Ideal R) = 1 := Ideal.one_eq_top.symm
  rw [htop]
  exact emultiplicity_of_one_right hunit

/-- A p-ordering is determined by infinitude, membership, and the
minimum condition at positive stages only: stage zero is automatic
since every stage-zero valuation equals zero, so `a 0` is arbitrary
within `S`. -/
theorem isPOrdering_iff_pos
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} :
    IsPOrdering p S a ↔
      S.Infinite ∧ (∀ n, a n ∈ S) ∧
        ∀ n, 1 ≤ n → ∀ x ∈ S,
          pOrderingValuation p a n (a n) ≤
            pOrderingValuation p a n x := by
  constructor
  · intro h
    exact ⟨h.infinite, h.mem, fun n _ x hx => h.min_le n x hx⟩
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro n x hx
    by_cases hn : 1 ≤ n
    · exact h.2.2 n hn x hx
    · have hn0 : n = 0 := by omega
      subst hn0
      rw [pOrderingValuation_zero, pOrderingValuation_zero]

end IsDedekindDomain.HeightOneSpectrum
