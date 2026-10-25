/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025. All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part4
import Instance.Combinatorics.Enumerative.AlternatingSums.Part2
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

/-- The set of split block indices for a subset S -/
def splitBlockIndices (d n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (n / d)).filter (fun i => isSplitBlock d n i S)

/-- The smallest split block index (as a natural number) -/
noncomputable def smallestSplitBlockIdx (d n : ℕ) (S : Finset ℕ) 
    (hne : (splitBlockIndices d n S).Nonempty) : ℕ :=
  (splitBlockIndices d n S).min' hne

/-! #### Bijection between blocky subsets and component pairs -/


/-- The backward map: (block indices, partial elements) → blocky subset -/
def componentsToSubset (d n : ℕ) (B P : Finset ℕ) : Finset ℕ :=
  let completeBlocks := B.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))
  let partialElems := P.image (fun p => (n / d) * d + p)
  completeBlocks ∪ partialElems

/-- The forward map: blocky subset → (block indices, partial elements) -/
def subsetToComponents (d n : ℕ) (S : Finset ℕ) : Finset ℕ × Finset ℕ :=
  let blockIndices := (Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)
  let partialElems := (Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)
  (blockIndices, partialElems)

/-! #### The Main Theorem -/
/-! ### q-Binomial Coefficients at q = -1

We compute `[n choose k]_{-1}` using the q-Lucas theorem with d=2 and ω=-1.
The result depends on the parities of `n` and `k`.

This is Exercise \ref{exe.sign.-1inom} in the source.
-/


/-- A blocky subset of `[n]` (when `n` is even) is a union of blocks `{0,1}, {2,3}, ...`.
Each block is either fully included or fully excluded. -/
def IsBlocky (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range n ∧
  ∀ i : ℕ, 2 * i + 1 < n → ((2 * i ∈ S) ↔ (2 * i + 1 ∈ S))

/-! ### Application: Sum of Signs of Acceptable Sets

We formalize the key step in the combinatorial proof of the negative hockey-stick identity:
the sum of signs of acceptable sets equals `(-1)^m * C(n-1, m)`.
-/

/-- The "moving" sets: acceptable sets whose partners are also acceptable. -/
def movingSets (n m : ℕ) : Finset (Finset ℕ) :=
  (acceptableSets n m).filter (fun I => partner I ∈ acceptableSets n m)

/-- The "fixed" sets: acceptable sets whose partners are not acceptable. -/
def fixedSets (n m : ℕ) : Finset (Finset ℕ) :=
  (acceptableSets n m).filter (fun I => partner I ∉ acceptableSets n m)

end AlgebraicCombinatorics.SignedCounting
