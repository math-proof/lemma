/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025. All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part4
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

/-! ### Acceptable Sets and Partners

We define acceptable sets (subsets of `{0, 1, ..., n-1}` with size at most `m`)
and the partner operation (symmetric difference with `{0}`).
-/


/-- The finset of acceptable sets: subsets of `Finset.range n` with cardinality at most `m`. -/
def acceptableSets (n m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun I => I.card ≤ m)

/-- The partner of a finite set `I` is `I △ {0}` (symmetric difference with singleton 0).
If `0 ∈ I`, this removes 0; if `0 ∉ I`, this adds 0. -/
def partner (I : Finset ℕ) : Finset ℕ :=
  symmDiff I {0}

/-- The sign of a finite set is `(-1)^|I|`. -/
def setSign (I : Finset ℕ) : ℤ :=
  (-1 : ℤ) ^ I.card

/-! ### The Negative Hockey-Stick Identity

The negative hockey-stick identity states:
`∑_{k=0}^{m} (-1)^k * C(n,k) = (-1)^m * C(n-1,m)`

This is Proposition \ref{prop.binom.nhs} in the source.
-/
/-! ### Cancellation Principles

These lemmas formalize the idea that sign-reversing bijections/involutions
cause addends to cancel in sums.
-/


section CancellationPrinciples

variable {α : Type*} [DecidableEq α] {R : Type*} [AddCommGroup R]

end CancellationPrinciples

/-! ### Switching Operation

The switching operation `switch_{i,i+1}` swaps elements `i` and `i+1` in a set
when exactly one of them is present.
-/


/-- Switch `i` with `i+1` in a set: if exactly one of `{i, i+1}` is in `S`,
replace it with the other; otherwise leave `S` unchanged. -/
def switch (i : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if (S ∩ {i, i + 1}).card = 1 then
    symmDiff S {i, i + 1}
  else S

/-! ### q-Binomial Coefficients

We define q-binomial coefficients and study their properties.
Note: As of this writing, q-binomial coefficients are not in Mathlib,
so we define them here.
-/


/-- The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q` where `[k]_q = 1 + q + q^2 + ... + q^{k-1}`.
We define it as a polynomial in `q`. -/
noncomputable def qFactorial (n : ℕ) : Polynomial ℤ :=
  ∏ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), Polynomial.X ^ i

/-- The q-binomial coefficient `[n choose k]_q = [n]_q! / ([k]_q! * [n-k]_q!)`.
This is well-defined as a polynomial (the division is exact).

We define it combinatorially using the sum over k-element subsets formula:
`[n choose k]_q = ∑_{S ⊆ [n], |S|=k} q^{sum(S) - (1+2+...+k)}`

**Note:** This is a local definition as `Polynomial ℤ`, equivalent to
`AlgebraicCombinatorics.qBinomial n k X` from `QBinomialBasic.lean` when the latter
is evaluated as a polynomial. The equivalence follows from `qBinomial_eq_sum_subsets`.
This definition uses 0-indexed sets `{0, 1, ..., n-1}` while `QBinomialBasic` uses
1-indexed sets `{1, 2, ..., n}` in its subset formula, but both are equivalent. -/
noncomputable def qBinomial (n k : ℕ) : Polynomial ℤ :=
  ∑ S ∈ (Finset.range n).powerset.filter (fun S => S.card = k),
    Polynomial.X ^ (S.sum id - (Finset.range k).sum id)

/-! ### Roots of Unity and Primitive Roots of Unity

This section formalizes Definition \ref{def.root-of-unity.prim} from the source.

**Definition (def.root-of-unity.prim):**
Let `K` be a field and `d` a positive integer.

**(a)** A *d-th root of unity* in `K` is an element `ω` of `K` satisfying `ω^d = 1`.
In other words, a d-th root of unity in `K` is an element of `K` whose d-th power is 1.

**(b)** A *primitive d-th root of unity* in `K` is an element `ω` of `K` satisfying
`ω^d = 1` but `ω^i ≠ 1` for each `i ∈ {1, 2, ..., d-1}`.
In other words, a primitive d-th root of unity in `K` is an element of the
multiplicative group `K×` whose order is exactly `d`.

**Mathlib correspondence:**
- Part (a) is captured by `ω ∈ rootsOfUnity d K` or equivalently `ω ^ d = 1`
- Part (b) is captured by `IsPrimitiveRoot ω d` from `RingTheory.RootsOfUnity.PrimitiveRoots`

**Key property:**
For `K = ℂ`, the d-th roots of unity are the `d` complex numbers
`e^{2πi·0/d}, e^{2πi·1/d}, ..., e^{2πi·(d-1)/d}` (vertices of a regular d-gon on the unit circle).
The primitive d-th roots of unity are those `e^{2πi·g/d}` where `gcd(g, d) = 1`.

In particular:
- The 2nd roots of unity in `ℂ` are `1` and `-1`
- The only primitive 2nd root of unity is `-1`
-/


section RootsOfUnity

variable {K : Type*} [CommRing K]

/-- An element `ω` is a *d-th root of unity* if `ω^d = 1`. (def.root-of-unity.prim (a))

This is the condition for membership in `rootsOfUnity d K` when `ω` is a unit.
For fields, we can state this directly without the unit requirement. -/
def IsRootOfUnity (ω : K) (d : ℕ) : Prop := ω ^ d = 1

variable [IsDomain K]

end RootsOfUnity

/-! #### Sum of Primitive Roots of Unity

A key property used in cancellation arguments: if `ω` is a primitive d-th root of unity
with `d > 1`, then `1 + ω + ω² + ... + ω^{d-1} = 0`.

This generalizes `1 + (-1) = 0` (the case `d = 2`) and allows cancellation in sums
involving powers of `ω`.

Note: Mathlib provides `IsPrimitiveRoot.geom_sum_eq_zero` which proves exactly this.
-/


section GeomSum

variable {K : Type*} [CommRing K] [IsDomain K]

end GeomSum

/-! ### The q-Lucas Theorem

The q-Lucas theorem relates q-binomial coefficients at primitive roots of unity
to ordinary binomial coefficients.
-/
/-! #### Helper Lemmas for q-Lucas -/
/-! ### Bridge to Canonical q-Binomial Definition

The local `qBinomial` definition uses 0-indexed k-subsets of `{0, 1, ..., n-1}`,
while the canonical `AlgebraicCombinatorics.qBinomialPoly` uses monotone functions.
This section proves they are equal.
-/
/-! #### d-Cycle Infrastructure for q-Lucas

The key to proving the q-Lucas theorem is the d-cycle cancellation argument.
For a primitive d-th root of unity ω, we have ∑_{j=0}^{d-1} ω^j = 0 (when d > 1).
This allows us to cancel contributions from subsets that don't respect the "block structure"
where blocks are consecutive intervals of size d.
-/


/-- A subset S of [n] is d-blocky if for each complete d-block {id, id+1, ..., id+d-1}
contained in [n], the set S either contains all elements or none of the elements. -/
def IsDBlocky (d n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range n ∧
  ∀ i < n / d,
    (∀ j < d, i * d + j ∈ S) ∨ (∀ j < d, i * d + j ∉ S)

end AlgebraicCombinatorics.SignedCounting
