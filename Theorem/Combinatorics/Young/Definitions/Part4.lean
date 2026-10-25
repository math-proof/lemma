/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.PowerSeries.CommutativeRings
import Def.Combinatorics.Young.Definitions.Part6
open scoped Polynomial
open MvPolynomial Finset

/-!
# Definitions and Examples of Symmetric Polynomials

This file formalizes the definitions and basic properties of symmetric polynomials,
following Section "Definitions and examples of symmetric polynomials" (sec.sf.sp) of the source.

## Main definitions

* We use Mathlib's `MvPolynomial.IsSymmetric` for the notion of symmetric polynomials.
* `MvPolynomial.symmetricSubalgebra σ R` is the ring of symmetric polynomials.
* `MvPolynomial.esymm σ R n` is the n-th elementary symmetric polynomial.
* `MvPolynomial.hsymm σ R n` is the n-th complete homogeneous symmetric polynomial.
* `MvPolynomial.psum σ R n` is the n-th power sum.

## Main results

* The symmetric group acts on polynomials by permuting variables (Proposition prop.sf.SN-acts)
* The action is by K-algebra automorphisms (Proposition prop.sf.SN-acts-by-alg-auts)
* The set of symmetric polynomials forms a K-subalgebra (Theorem thm.sf.S-subalg)
* For n > N, the n-th elementary symmetric polynomial is zero (Proposition prop.sf.en=0)
* Newton-Girard formulas relating e_n, h_n, and p_n (Theorem thm.sf.NG)
* Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)
* A polynomial is symmetric iff it is invariant under simple transpositions (Lemma lem.sf.simples-enough)

## References

* Source: SymmetricFunctions/Definitions.tex, sec.sf.sp

## Implementation notes

Mathlib already provides extensive support for symmetric polynomials via `MvPolynomial.IsSymmetric`
and related definitions. This file connects the textbook presentation to Mathlib's API
and provides additional lemmas following the source material.

The symmetric group action on polynomials is given by `MvPolynomial.rename` in Mathlib.
For a permutation σ : Equiv.Perm (Fin N), the action σ · f is `MvPolynomial.rename σ f`.
-/


/-! Compatibility with the pre-2026 `MvPolynomial.coeff m p` argument order. -/


namespace AlgebraicCombinatorics

namespace SymmetricPolynomials

variable {K : Type*} [CommRing K]

variable {N : ℕ}

variable {σ : Type*}

section WithDecidableEq'

variable [DecidableEq (Fin N)]

/-! ### Helper lemmas for the bijection in Newton-Girard hp formula -/


/-- Helper: replicate n a ≤ s iff n ≤ count a s. -/
theorem replicate_le_iff_count {α : Type*} [DecidableEq α] (a : α) (m : ℕ) (s : Multiset α) :
    Multiset.replicate m a ≤ s ↔ m ≤ s.count a := by
  constructor
  · intro h
    calc m = (Multiset.replicate m a).count a := by simp
      _ ≤ s.count a := Multiset.count_le_of_le a h
  · intro h
    rw [Multiset.le_iff_count]
    intro b
    simp only [Multiset.count_replicate]
    split_ifs with heq
    · subst heq; exact h
    · exact Nat.zero_le _

/-- Cardinality of s - replicate (k+1) i when k < count i s. -/
theorem sub_replicate_card (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    (s.1 - Multiset.replicate (k + 1) i).card = m - 1 - k := by
  have hle : Multiset.replicate (k + 1) i ≤ s.1 := by
    rw [replicate_le_iff_count]; omega
  rw [Multiset.card_sub hle, s.2, Multiset.card_replicate]
  omega

omit [DecidableEq (Fin N)] in
/-- Cardinality of t + replicate (j+1) i when j < n. -/
theorem add_replicate_card (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    (t.1 + Multiset.replicate (j + 1) i).card = m := by
  rw [Multiset.card_add, t.2, Multiset.card_replicate]
  omega

end WithDecidableEq'
end SymmetricPolynomials
end AlgebraicCombinatorics
