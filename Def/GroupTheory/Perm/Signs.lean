/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.GroupTheory.Perm.Inversions1
open Equiv Equiv.Perm Finset BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

/-!
# Signs of Permutations

This file formalizes the notion of the sign (signature) of a permutation and its properties.

The sign of a permutation σ ∈ Sₙ is defined as (-1)^ℓ(σ) where ℓ(σ) is the length
(number of inversions) of σ. This is a fundamental concept in combinatorics and algebra,
playing a crucial role in the definition of determinants and exterior powers.

## Main definitions

Most definitions are already in Mathlib:
* `Equiv.Perm.sign` - the sign of a permutation as a group homomorphism to ℤˣ
* `alternatingGroup` - the alternating group (kernel of the sign homomorphism)

We provide:
* `Equiv.Perm.IsEven` - a permutation is even if its sign is 1
* `Equiv.Perm.IsOdd` - a permutation is odd if its sign is -1

## Main results

### Properties of the sign (Proposition prop.perm.sign.props)

* `Equiv.Perm.sign_one` (a): sign(id) = 1
* `Equiv.Perm.sign_swap` (b): sign(t_{i,j}) = -1 for distinct i, j
* `Equiv.Perm.sign_cycle` (c): sign of a k-cycle is (-1)^(k-1)
* `Equiv.Perm.sign_mul` (d): sign(στ) = sign(σ) · sign(τ)
* `sign_prod_list` (e): sign of a product equals product of signs
* `Equiv.Perm.sign_inv` (f): sign(σ⁻¹) = sign(σ)
* `sign_eq_prod_pairs` (g): sign as product over pairs
* `prod_diff_comp_perm` (h): product formula for differences

### The sign homomorphism (Corollary cor.perm.sign.hom)

* `Equiv.Perm.sign` is a group homomorphism from Sₙ to {1, -1}

### The alternating group (Corollary cor.perm.altgp)

* `alternatingGroup.normal` - the alternating group is normal in Sₙ

### Counting even/odd permutations (Corollary cor.perm.num-even)

* `card_alternatingGroup` - |Aₙ| = n!/2 for n ≥ 2
* `sum_sign_eq_zero` - Σ_{σ ∈ Sₙ} sign(σ) = 0 for n ≥ 2

### Sign for finite sets (Proposition prop.perm.sign.X)

* Sign can be defined for permutations of any finite set X, independent of chosen bijection

## References

* [Darij Grinberg, *Notes on the combinatorial fundamentals of algebra*][detnotes]
* [Neil Strickland, *Combinatorics and algebra*][Strick13]

## Tags

permutation, sign, signature, alternating group, parity
-/


/-! ### Definition of sign

The sign of a permutation σ is (-1)^ℓ(σ) where ℓ(σ) is the length (number of inversions).
In Mathlib, this is `Equiv.Perm.sign`.

**Definition (def.perm.sign)**: For n ∈ ℕ, the sign of σ ∈ Sₙ is (-1)^ℓ(σ).
It is denoted (-1)^σ, sgn(σ), sign(σ), or ε(σ).
-/


/-!
### Proof that sign σ = (-1)^ℓ(σ)

The fundamental theorem connecting the Mathlib definition of `Equiv.Perm.sign`
(which uses a product formula) with the textbook definition sign(σ) = (-1)^ℓ(σ)
where ℓ(σ) is the number of inversions.

This formalizes **Definition (def.perm.sign)**.
-/


section SignDefinition
variable {n : ℕ}

end SignDefinition

namespace Equiv.Perm

/-- A permutation is **even** if its sign is 1 (equivalently, if its length is even).
**Definition (def.perm.even-odd)** -/
def IsEven (σ : Perm α) : Prop := sign σ = 1

/-- A permutation is **odd** if its sign is -1 (equivalently, if its length is odd).
**Definition (def.perm.even-odd)** -/
def IsOdd (σ : Perm α) : Prop := sign σ = -1

end Equiv.Perm
