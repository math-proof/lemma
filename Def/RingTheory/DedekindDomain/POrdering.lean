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

end IsDedekindDomain.HeightOneSpectrum
