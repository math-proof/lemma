/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Project Contributors
Authors: AlgebraicCombinatorics Project Contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.Basics.Part8
import Abbrev.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part2
open scoped Nat PowerSeries

/-!
# Euler's Pentagonal Number Theorem and Jacobi's Triple Product Identity

This file formalizes Euler's pentagonal number theorem and Jacobi's triple product identity,
following the treatment in the AlgebraicCombinatorics textbook.

## Main definitions

* `pentagonalNumber` : The k-th pentagonal number w_k = (3k - 1) * k / 2
* `Level` : A "level" is a half-integer p + 1/2 for some integer p (used in the proof)
* `State` : A "state" is a set of levels containing all but finitely many negative levels
  and only finitely many positive levels
* `State.energy` : The energy of a state
* `State.parnum` : The particle number of a state

## Main results

* `pentagonalNumber_nonneg` : Pentagonal numbers are nonnegative
* `euler_pentagonal_number_theorem` : ∏_{k≥1} (1 - x^k) = ∑_{k∈ℤ} (-1)^k x^{w_k}
* `jacobi_triple_product` : Jacobi's triple product identity
* `partition_recursive` : Recursive formula for partition numbers using pentagonal numbers
* `euler_sum_divisors_recursive` : Euler's recursion for the sum of divisors function

## References

* AlgebraicCombinatorics textbook, Section on Partitions/PentagonalJacobi.tex
* [Bell, 2006] for history of Euler's pentagonal number theorem
* [Borcherds' proof via Cameron's book, §8.3]

## Tags

pentagonal number, Euler, Jacobi triple product, partitions, formal power series
-/


namespace AlgebraicCombinatorics

section Jacobi

variable {R : Type*} [CommRing R]

/-- The Laurent polynomial variable z, viewed as a constant power series in JacobiRing.
This represents z = T(1) where T is the Laurent polynomial basis element. -/
noncomputable def jacobiZ : JacobiRing := PowerSeries.C (LaurentPolynomial.T 1)

/-- The inverse z^{-1} = T(-1) as a constant power series. -/
noncomputable def jacobiZInv : JacobiRing := PowerSeries.C (LaurentPolynomial.T (-1))

/-- z^ℓ for any integer ℓ, as a constant power series. -/
noncomputable def jacobiZPow (ell : ℤ) : JacobiRing := PowerSeries.C (LaurentPolynomial.T ell)

/-- The factor (1 + q^{2n-1}z) in Jacobi's product, for n ≥ 1.
Here we index by n starting from 0, so the exponent is 2n+1. -/
noncomputable def jacobiFactorZ (n : ℕ) : JacobiRing :=
  1 + PowerSeries.X ^ (2 * n + 1) * jacobiZ

/-- The factor (1 + q^{2n-1}z^{-1}) in Jacobi's product. -/
noncomputable def jacobiFactorZInv (n : ℕ) : JacobiRing :=
  1 + PowerSeries.X ^ (2 * n + 1) * jacobiZInv

/-- The factor (1 - q^{2n}) in Jacobi's product.
Here we index by n starting from 0, so the exponent is 2(n+1). -/
noncomputable def jacobiFactorQ (n : ℕ) : JacobiRing :=
  1 - PowerSeries.X ^ (2 * (n + 1))

/-- A single term in Jacobi's product:
  (1 + q^{2n-1}z)(1 + q^{2n-1}z^{-1})(1 - q^{2n})
indexed starting from n = 0 (corresponding to n = 1 in the mathematical formula). -/
noncomputable def jacobiProductTerm (n : ℕ) : JacobiRing :=
  jacobiFactorZ n * jacobiFactorZInv n * jacobiFactorQ n

/-- The left-hand side of Jacobi's triple product identity in JacobiRing:
  ∏_{n>0} ((1 + q^{2n-1}z)(1 + q^{2n-1}z^{-1})(1 - q^{2n}))

This is defined as an infinite product using the discrete topology on LaurentPolynomial ℤ
and the product topology on PowerSeries. -/
noncomputable def jacobiLHS' : JacobiRing :=
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  haveI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := LaurentPolynomial ℤ)
  ∏' n, jacobiProductTerm n

/-- A single term q^{ℓ²} z^ℓ in Jacobi's sum. -/
noncomputable def jacobiSumTerm (ell : ℤ) : JacobiRing :=
  PowerSeries.X ^ ell.natAbs ^ 2 * jacobiZPow ell

/-- The right-hand side of Jacobi's triple product identity in JacobiRing:
  ∑_{ℓ∈ℤ} q^{ℓ²} z^ℓ

This is defined as an infinite sum over ℤ. The sum is well-defined because
the exponent ℓ² grows quadratically, so only finitely many terms contribute
to each coefficient of q. -/
noncomputable def jacobiRHS' : JacobiRing :=
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  haveI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := LaurentPolynomial ℤ)
  ∑' ell : ℤ, jacobiSumTerm ell

/-! ### Helper lemmas for Jacobi's triple product identity -/
/-! ### State Monomials

The following definitions and lemmas connect the algebraic terms in Jacobi's identity
to the state-based proof infrastructure. A "state monomial" q^e * z^p represents
a state with energy e and particle number p.
-/


/-- The monomial q^e * z^p in JacobiRing, representing a state with energy e and particle number p.
This is the building block for the state generating function. -/
noncomputable def stateMonomial (e : ℕ) (p : ℤ) : JacobiRing :=
  PowerSeries.X ^ e * jacobiZPow p

/-- The state generating function in JacobiRing:
  ∑_{S state} q^{energy(S)} z^{parnum(S)}

In Borcherds' proof, this is the key object that both the LHS and RHS of Jacobi's
triple product identity equal (after multiplying by the partition generating function).

Since states are in bijection with pairs (ℓ, μ) where ℓ ∈ ℤ and μ is a partition
(via `partitionToState_bijective`), and the bijection satisfies:
- energy(E_{ℓ,μ}) = ℓ² + 2|μ| (by `excitedState_energy`)
- parnum(E_{ℓ,μ}) = ℓ (by `excitedState_parnum`)

we can write the state generating function as:
  ∑_{ℓ∈ℤ} ∑_{n≥0} ∑_{μ partition of n} q^{ℓ² + 2n} z^ℓ

This equals:
  ∑_{ℓ∈ℤ} q^{ℓ²} z^ℓ · ∑_{n≥0} (number of partitions of n) · q^{2n}

which is jacobiRHS' · partitionGenFun[q²].
-/
noncomputable def stateGenFun : JacobiRing :=
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  haveI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := LaurentPolynomial ℤ)
  ∑' (pair : ℤ × (Σ n, Nat.Partition n)),
    let ℓ := pair.1
    let n := pair.2.1
    stateMonomial (ℓ.natAbs ^ 2 + 2 * n) ℓ

/-- The partition generating function in JacobiRing with q replaced by q².

This is ∑_{n≥0} p(n) q^{2n} where p(n) is the number of partitions of n.
Equivalently, it's the image of the partition generating function under the
substitution q ↦ q².

This is a key ingredient in proving Jacobi's triple product identity:
  stateGenFun = jacobiRHS' * partitionGenFunJacobi

Note: We define this as a sum over partitions rather than using the product
formula ∏_{k≥1}(1-q^{2k})^{-1} to match the structure of stateGenFun. -/
noncomputable def partitionGenFunJacobi : JacobiRing :=
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  haveI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := LaurentPolynomial ℤ)
  ∑' (p : Σ n, Nat.Partition n), PowerSeries.X ^ (2 * p.1)

/-- The product of Z and ZInv factors (without the Q factor):
  ∏_{n>0} ((1 + q^{2n-1}z)(1 + q^{2n-1}z^{-1}))
This is the product that remains after canceling the (1-q^{2n}) factors. -/
noncomputable def jacobiZZProduct : JacobiRing :=
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  haveI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := LaurentPolynomial ℤ)
  ∏' n, (jacobiFactorZ n * jacobiFactorZInv n)

/-- The Euler product (Q factors only):
  ∏_{n>0} (1 - q^{2n})
This is the product that cancels with partitionGenFunJacobi. -/
noncomputable def jacobiQProduct : JacobiRing :=
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  haveI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := LaurentPolynomial ℤ)
  ∏' n, jacobiFactorQ n

/-! ### Helper lemmas for the odd case proof

These lemmas prove that the infinite product of power series with only even-degree terms
also has only even-degree terms. This is used to show that the coefficient at odd degree
in the product is 0.
-/
/-! ### Helper lemmas for the even case of partitionGenFunJacobi_mul_QProduct_eq_one

These lemmas prove that the coefficient at 2*n in the JacobiRing product equals Nat.card (n.Partition).
The key insight is that the JacobiRing product equals the image of the ℤ⟦X⟧ product under
`PowerSeries.map (algebraMap ℤ (LaurentPolynomial ℤ))`, and the ℤ⟦X⟧ product equals
`expand 2 (Nat.Partition.genFun (fun _ _ => 1))`.
-/
/-! ### Explicit formulas for Jacobi factors

These lemmas give explicit formulas for jacobiFactorZ n - 1 and jacobiFactorZInv n - 1,
which are used in the binary expansion proof.
-/
/-! ### (P, N) to State Bijection Infrastructure

The bijection between pairs (P, N) of finite subsets of ℕ and states is key to
proving `jacobiZZProduct_eq_stateGenFun`. Here we define the level set map and prove its properties.

Given (P, N):
- P represents the set of nonnegative integers in the state (positive half-integer levels)
- N represents the set of n such that -n-1 is NOT in the state (missing negative levels)

Note: The actual State definition is later in the file. The `finsetPairToState` function
is defined after State.
-/


/-- The set of levels corresponding to a pair (P, N) of finite subsets of ℕ.

The state S has:
- All negative levels except {-n-1 : n ∈ N}
- Exactly the levels in P among nonnegative levels -/
def finsetPairToStateLevels (P N : Finset ℕ) : Set ℤ :=
  {p : ℤ | p < 0 ∧ ((-p - 1).toNat ∉ N)} ∪ {p : ℤ | ∃ n ∈ P, p = n}

/-! ### Binary Expansion Infrastructure

The following lemmas establish the binary expansion formula for infinite products:
  ∏' n, (1 + a_n) = ∑' P : Finset ℕ, ∏ n ∈ P, a_n

This is the key ingredient for proving `jacobiZZProduct_eq_stateGenFun`.
-/

-- Note: jacobi_triple_product_fps' is defined later in the file (in section MovedLemmas
-- after finsetPair_sum_eq_partition_sum) because it depends on
-- stateGenFun_eq_jacobiLHS'_mul_partitionGenFunJacobi which uses the State infrastructure.


/-- The left-hand side of Jacobi's triple product identity evaluated at q = u·x^a, z = v·x^b:
  ∏_{n>0} ((1 + q^{2n-1}z)(1 + q^{2n-1}z^{-1})(1 - q^{2n}))

Expanding with q = u·x^a and z = v·x^b:
  ∏_{n>0} ((1 + u^{2n-1}v·x^{(2n-1)a+b})(1 + u^{2n-1}v^{-1}·x^{(2n-1)a-b})(1 - u^{2n}·x^{2na}))

When a > 0 and a ≥ |b|, all exponents (2n-1)a+b, (2n-1)a-b, and 2na are nonnegative
for n > 0, so this is a well-defined element of ℚ⟦X⟧.
The infinite product is multipliable because the exponents grow linearly in n.
-/
noncomputable def jacobiLHSEval (a b : ℤ) (u v : ℚ) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  -- n ranges over positive integers, so we index by ℕ with n = k + 1
  ∏' k : ℕ,
    let n := k + 1
    let exp1 := ((2 * n - 1) * a + b).toNat  -- (2n-1)a + b
    let exp2 := ((2 * n - 1) * a - b).toNat  -- (2n-1)a - b
    let exp3 := (2 * n * a).toNat            -- 2na
    let coeff1 := u^(2*n - 1) * v            -- u^{2n-1} * v
    let coeff2 := u^(2*n - 1) * v⁻¹          -- u^{2n-1} * v^{-1}
    let coeff3 := u^(2*n)                    -- u^{2n}
    ((1 : ℚ⟦X⟧) + (coeff1 : ℚ) • PowerSeries.X ^ exp1) *
    ((1 : ℚ⟦X⟧) + (coeff2 : ℚ) • PowerSeries.X ^ exp2) *
    ((1 : ℚ⟦X⟧) - (coeff3 : ℚ) • PowerSeries.X ^ exp3)

/-- The right-hand side of Jacobi's triple product identity evaluated at q = u·x^a, z = v·x^b:
  ∑_{ℓ∈ℤ} q^{ℓ²} z^ℓ = ∑_{ℓ∈ℤ} u^{ℓ²} v^ℓ x^{aℓ² + bℓ}

When a > 0 and a ≥ |b|, the exponent aℓ² + bℓ ≥ 0 for all ℓ ∈ ℤ, since:
  aℓ² + bℓ ≥ |b|·ℓ² - |b|·|ℓ| = |b|·|ℓ|·(|ℓ| - 1) ≥ 0

This is a well-defined element of ℚ⟦X⟧.
The infinite sum is summable because the exponent aℓ² + bℓ grows quadratically in |ℓ|.
-/
noncomputable def jacobiRHSEval (a b : ℤ) (u v : ℚ) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  -- Use zpow for v^ℓ to handle negative ℓ
  ∑' ℓ : ℤ, (u^(ℓ^2).natAbs * v^ℓ : ℚ) • PowerSeries.X ^ (a * ℓ^2 + b * ℓ).toNat

/-- The partition generating function evaluated at q = u·x^a:
  ∏_{k>0} (1 - q^{2k})^{-1} = ∏_{k>0} (1 - u^{2k}·x^{2ka})^{-1}

When a > 0, all exponents 2ka are positive for k > 0, so this is well-defined
as a formal power series. The constant term is 1, so it is a unit in ℚ⟦X⟧.

This represents the generating function for partitions where each part
contributes q^{2·part} to the weight. -/
noncomputable def partitionGenFunEval (a : ℤ) (u : ℚ) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  -- The inverse of ∏_{k>0} (1 - u^{2k}·x^{2ka})
  -- We define it as ∑_{μ partition} u^{2|μ|}·x^{2a|μ|}
  ∑' p : Σ n, Nat.Partition n, (u^(2*p.1) : ℚ) • PowerSeries.X ^ (2 * a * p.1).toNat

/-- The Euler product with parameters: ∏_{k>0}(1 - u^{2k}·X^{2ak}).
This is the product that cancels with `partitionGenFunEval`. -/
noncomputable def eulerProductParam (a : ℤ) (u : ℚ) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  ∏' k : ℕ, (1 - (u^(2*(k+1)) : ℚ) • (PowerSeries.X : ℚ⟦X⟧) ^ (2 * a * (k + 1)).toNat)

end Jacobi
end AlgebraicCombinatorics
