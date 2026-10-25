/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025. All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part4
import Def.Combinatorics.Enumerative.AlternatingSums
/-!
# Cancellations in Alternating Sums

This file formalizes the theory of cancellations in alternating sums using
sign-reversing bijections and involutions. The main results include:

* The negative hockey-stick identity for binomial coefficients
* Three versions of the cancellation principle (Lemmas `sign_cancel1`, `sign_cancel2`, `sign_cancel3`)
* The evaluation of q-binomial coefficients at q = -1
* The q-Lucas theorem for primitive roots of unity

## Main definitions

* `acceptableSets`: A finset of subsets of `Finset.range n` with cardinality at most `m`
* `partner`: The symmetric difference of a set with `{0}`, used for sign-reversing
* `setSign`: The sign `(-1)^|I|` of a finite set `I`
* `switch`: Swap elements `i` and `i+1` in a set when exactly one is present
* `IsBlocky`: A subset that is a union of consecutive pairs (blocks)
* `IsRootOfUnity`: An element `ω` satisfying `ω^d = 1`
* `qBinomial`: The q-binomial coefficient `[n choose k]_q` (local definition as `Polynomial ℤ`)

## Main results

* `negHockeyStick`: The negative hockey-stick identity
  `∑ k ∈ Finset.range (m+1), (-1)^k * (n.choose k) = (-1)^m * (n-1).choose m`
* `sign_cancel1`: Cancellation principle for sign-reversing bijections
* `sign_cancel2`: Cancellation principle for sign-reversing involutions without fixed points
* `sign_cancel3`: Cancellation principle for sign-reversing involutions with zero-sign fixed points
* `qBinom_neg_one`: Formula for q-binomial coefficients evaluated at q = -1
* `qLucas`: The q-Lucas theorem for primitive roots of unity
* `qBinomial_eq_canonical`: Bridge lemma connecting local `qBinomial` to `AlgebraicCombinatorics.qBinomialPoly`

**Note on qBinomial:** This file defines a local `qBinomial` as a `Polynomial ℤ` using
the subset sum formula. This is equivalent to `AlgebraicCombinatorics.qBinomialPoly` in
`QBinomialBasic.lean`. The theorem `qBinomial_eq_canonical` proves this equivalence.
The local definition is in namespace `AlgebraicCombinatorics.SignedCounting` to avoid conflicts.

## References

* Section on "Cancellations in alternating sums" from Algebraic Combinatorics notes
* Labels: prop.binom.nhs, lem.sign.cancel1, lem.sign.cancel2, lem.sign.cancel3,
  exe.sign.-1inom, def.root-of-unity.prim, thm.sign.q-lucas

## Tags

alternating sums, sign-reversing involution, cancellation principle, q-binomial,
hockey-stick identity, roots of unity, q-Lucas theorem
-/


namespace AlgebraicCombinatorics.SignedCounting

open Finset BigOperators

instance decidableIsDBlocky (d n : ℕ) (S : Finset ℕ) : Decidable (IsDBlocky d n S) := by
  unfold IsDBlocky
  infer_instance

end AlgebraicCombinatorics.SignedCounting
