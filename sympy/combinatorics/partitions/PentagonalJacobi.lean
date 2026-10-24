/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Project Contributors
Authors: AlgebraicCombinatorics Project Contributors
-/
import Mathlib
import sympy.combinatorics.partitions.Basics
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


open scoped Nat PowerSeries

namespace AlgebraicCombinatorics
/-! ## Pentagonal Numbers -/


/-- The k-th pentagonal number, defined as w_k = (3k - 1) * k / 2.
This is always a nonnegative integer for any k ∈ ℤ.
(Definition \ref{def.pars.pent-num}) -/
def pentagonalNumber (k : ℤ) : ℕ :=
  ((3 * k - 1) * k / 2).toNat

/-- Key bound: w_k ≥ |k| for k ≠ 0.
This is because for k ≥ 1: (3k-1)k/2 ≥ k, and for k ≤ -1: (3|k|+1)|k|/2 ≥ |k|. -/
theorem pentagonalNumber_ge_natAbs {k : ℤ} (hk : k ≠ 0) :
    pentagonalNumber k ≥ k.natAbs := by
  unfold pentagonalNumber
  by_cases hpos : k > 0
  · have hk1 : k ≥ 1 := hpos
    have h1 : (3 * k - 1) * k / 2 ≥ k := by
      have h2 : 3 * k - 1 ≥ 2 := by omega
      have h3 : (3 * k - 1) * k ≥ 2 * k := by nlinarith
      omega
    have habs : k.natAbs = k.toNat := by omega
    rw [habs]
    exact Int.toNat_le_toNat h1
  · push Not at hpos
    have hneg : k < 0 := by omega
    let m := -k
    have hm : m ≥ 1 := by omega
    have heq : (3 * k - 1) * k = (3 * m + 1) * m := by ring
    have h1 : (3 * m + 1) * m / 2 ≥ m := by
      have h2 : 3 * m + 1 ≥ 2 := by omega
      have h3 : (3 * m + 1) * m ≥ 2 * m := by nlinarith
      omega
    have habs : k.natAbs = m.toNat := by omega
    rw [heq, habs]
    exact Int.toNat_le_toNat h1

/-- The set of k with pentagonalNumber k < n is finite, since pentagonal numbers grow quadratically. -/
theorem pentagonal_below_finite (n : ℕ) : Set.Finite {k : ℤ | pentagonalNumber k < n} := by
  have h : {k : ℤ | pentagonalNumber k < n} ⊆ Set.Icc (-(n : ℤ)) n := by
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    simp only [Set.mem_Icc]
    by_cases hk0 : k = 0
    · subst hk0; omega
    · have hge := pentagonalNumber_ge_natAbs hk0
      have hlt : k.natAbs < n := Nat.lt_of_le_of_lt hge hk
      constructor
      · have h1 : -(k.natAbs : ℤ) ≤ k := by
          have := Int.neg_le_neg_iff.mpr (Int.le_natAbs (a := -k))
          simp at this
          convert this using 1
          simp
        omega
      · have h2 : k ≤ k.natAbs := Int.le_natAbs
        omega
  exact Set.Finite.subset (Set.finite_Icc _ _) h

/-- The subtype {k : ℤ // pentagonalNumber k < n} is finite. -/
instance pentagonal_below_fintype (n : ℕ) : Finite {k : ℤ // pentagonalNumber k < n} := by
  have := pentagonal_below_finite n
  exact Set.finite_coe_iff.mpr this
/-! ## Formal Power Series Setup -/


section FPS

variable {R : Type*} [CommRing R]

/-- Helper: Check if n is a pentagonal number and return the corresponding k.
Returns none if n is not a pentagonal number.

This is computable for any given n by checking a finite range of k values,
since pentagonal numbers grow quadratically. -/
def pentagonalNumberInverse (n : ℕ) : Option ℤ :=
  -- For any n, we only need to check k in a bounded range
  -- since w_k grows roughly like 3k²/2
  let bound := n + 1
  -- Check positive k first, then negative k
  let posResult := (List.range bound).find? fun k => pentagonalNumber k = n
  match posResult with
  | some k => some k
  | none =>
    let negResult := (List.range bound).find? fun k => pentagonalNumber (-(k : ℤ) - 1) = n
    match negResult with
    | some k => some (-(k : ℤ) - 1)
    | none => none

/-- The coefficient of x^n in the pentagonal series.
Returns (-1)^k if n = w_k for some k, and 0 otherwise.

Note: We use `k.natAbs` to compute the sign correctly for negative k,
since (-1)^k = (-1)^|k| for integers (as (-1)^{-m} = (-1)^m). -/
def pentagonalCoeff (n : ℕ) : ℤ :=
  match pentagonalNumberInverse n with
  | some k => (-1 : ℤ) ^ k.natAbs
  | none => 0

/-- The alternating sum ∑_{k∈ℤ} (-1)^k x^{w_k} as a formal power series.
This is well-defined because the pentagonal numbers grow quadratically.

We define the coefficient at n to be (-1)^k if n = w_k for some k, and 0 otherwise.
Since pentagonal numbers are injective, this is well-defined. -/
noncomputable def pentagonalSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => (pentagonalCoeff n : R)

/-- The Euler product ∏_{k≥1} (1 - x^k).

This is defined using the discrete topology on R, which ensures the infinite product
is well-defined via Mathlib's infrastructure for infinite products of power series.
The product is multipliable because the order of (1 - X^k) is k, which tends to infinity. -/
noncomputable def eulerProduct : R⟦X⟧ :=
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := R)
  ∏' k, (1 - PowerSeries.X ^ (k + 1) : R⟦X⟧)

end FPS
/-! ## Euler's Pentagonal Number Theorem

Note: The theorem `euler_pentagonal_number_theorem` is defined later in this file
(after `euler_pentagonal_number_theorem_rat`) due to dependency ordering.
See the section "Euler's Pentagonal Number Theorem (Main Result)" below.
-/
/-! ## Recursive Formula for Partition Numbers -/


/-- Local alias for `Nat.Partition.partitionCount` from `Partitions/Basics.lean`.
This provides compatibility with existing code in this file. -/
abbrev partitionCount := Nat.Partition.partitionCount

/-- The generating function for partitions as a formal power series.
  ∑_{n∈ℕ} p(n) x^n -/
noncomputable def partitionGenFun : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => partitionCount n

/-- The inverse Euler product ∏_{k≥1} 1/(1-x^k).

This is defined using Mathlib's partition generating function framework.
By `Nat.Partition.genFun_eq_tprod`, this equals:
  ∏' i, (1 + ∑' j, X ^ ((i + 1) * (j + 1)))
which is the product ∏_{k≥1} (1 + X^k + X^{2k} + ...) = ∏_{k≥1} 1/(1-X^k). -/
noncomputable def eulerProductInv : ℤ⟦X⟧ := Nat.Partition.genFun (fun _ _ => 1)

section eulerProductProof

open PowerSeries.WithPiTopology


-- Set up the discrete topology on ℤ and the product topology on ℤ⟦X⟧
attribute [local instance] instTopologicalSpace


-- Provide the T2Space instance for ℤ⟦X⟧ with discrete topology on ℤ
theorem instT2SpaceInt : @T2Space ℤ⟦X⟧ (instTopologicalSpace ℤ) :=
  @instT2Space ℤ ⊥ (@DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩)
attribute [local instance] instT2SpaceInt

end eulerProductProof
/-! ## Jacobi's Triple Product Identity -/

-- Note: The recursive formula `partition_recursive` is defined later in this file,
-- after `partitionGenFun_mul_pentagonalSeries` and `euler_pentagonal_number_theorem`.


section Jacobi

variable {R : Type*} [CommRing R]

/-- The ring (ℤ[z^±])[[q]] for Jacobi's triple product identity.
This is the ring of formal power series in q with coefficients that are
Laurent polynomials in z over ℤ. -/
abbrev JacobiRing := PowerSeries (LaurentPolynomial ℤ)

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
/-! ### Helper lemmas for exponent calculations

These lemmas establish key properties of the scaled exponents `(2 * a * (k + 1)).toNat`
used in the partition generating function identity. -/
/-! ### Partition sum and product formulas

These lemmas relate the multiset sum of a partition to the Finsupp representation,
which is key for proving the partition generating function identity. -/
/-! ### Helper lemmas for parameterized product expansion

These lemmas compute the explicit form of the finite products of parameterized factors.
They are used in the proof of `jacobiLHS_mul_partitionGenFun` to connect the binary
expansion of the product to the sum over (ℓ, μ) pairs.
-/
/-! ## Proof Infrastructure: States and Levels -/


/-- A "level" is a half-integer, represented as p + 1/2 for some integer p.
We represent it simply by the integer p. -/
abbrev Level := ℤ

/-- A "state" is a set of levels that contains all but finitely many negative levels
and only finitely many positive levels.

This is used in Borcherds' proof of Jacobi's triple product identity.

**Important convention**: A "level" in the tex source is a half-integer `p + 1/2` for some integer p.
We represent it by the integer p. Thus:
- "positive level" in the tex source means `p + 1/2 > 0`, i.e., `p ≥ 0` in our representation
- "negative level" in the tex source means `p + 1/2 < 0`, i.e., `p < 0` in our representation

The structure tracks:
- `finite_nonneg`: the set of nonnegative integers p (representing positive half-integer levels) in S
- `finite_negative_missing`: the set of negative integers p (representing negative half-integer levels) NOT in S -/
structure State where
  /-- The set of levels in this state -/
  levels : Set Level
  /-- Only finitely many nonnegative levels (p ≥ 0, representing positive half-integers p+1/2 > 0) are in the state -/
  finite_nonneg : Set.Finite {p : Level | p ≥ 0 ∧ p ∈ levels}
  /-- Only finitely many negative levels (p < 0, representing negative half-integers p+1/2 < 0) are NOT in the state -/
  finite_negative_missing : Set.Finite {p : Level | p < 0 ∧ p ∉ levels}

namespace State

/-- The energy of a state S is:
  energy(S) = ∑_{p≥0, p∈S} (2p+1) - ∑_{p<0, p∉S} (2p+1)

In the tex source, levels are half-integers `q = p + 1/2`, and the formula is:
  energy(S) = ∑_{q>0, q∈S} 2q - ∑_{q<0, q∉S} 2q

Substituting q = p + 1/2:
- q > 0 ⟺ p ≥ 0
- 2q = 2(p + 1/2) = 2p + 1

For p ≥ 0: 2p + 1 = 2*p.natAbs + 1 (since p.natAbs = p for p ≥ 0)
For p < 0: -(2p + 1) = -2p - 1 = 2*|p| - 1 = 2*p.natAbs - 1 (since p.natAbs = -p for p < 0)

Thus energy is always a natural number. -/
noncomputable def energy (S : State) : ℕ :=
  (S.finite_nonneg.toFinset.sum fun p => 2 * p.natAbs + 1) +
  (S.finite_negative_missing.toFinset.sum fun p => 2 * p.natAbs - 1)

/-- The particle number of a state S is:
  parnum(S) = #{p ≥ 0 : p ∈ S} - #{p < 0 : p ∉ S}

In the tex source, this counts the number of positive half-integer levels in S
minus the number of negative half-integer levels not in S. -/
noncomputable def parnum (S : State) : ℤ :=
  S.finite_nonneg.toFinset.card - S.finite_negative_missing.toFinset.card

/-- The ℓ-ground state G_ℓ = {all levels < ℓ}.

In the half-integer convention, G_ℓ contains all half-integer levels q < ℓ.
In our integer representation (where level q = p + 1/2), this is {p : p < ℓ}.

For ℓ ≥ 0:
- Nonnegative integers in G_ℓ: {0, 1, ..., ℓ-1}
- No negative integers are missing from G_ℓ

For ℓ < 0:
- No nonnegative integers are in G_ℓ
- Negative integers missing from G_ℓ: {ℓ, ℓ+1, ..., -1} -/
def groundState (ell : ℤ) : State where
  levels := {p : Level | p < ell}
  finite_nonneg := by
    by_cases h : ell ≤ 0
    · convert Set.finite_empty
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hp
      linarith
    · push Not at h
      apply Set.Finite.subset (Set.finite_Ico 0 ell)
      intro p ⟨hp_nonneg, hp_lt⟩
      simp only [Set.mem_Ico]
      exact ⟨hp_nonneg, hp_lt⟩
  finite_negative_missing := by
    by_cases h : ell ≥ 0
    · convert Set.finite_empty
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hp
      push Not
      linarith
    · push Not at h
      apply Set.Finite.subset (Set.finite_Ico ell 0)
      intro p ⟨hp_neg, hp_ge⟩
      simp only [Set.mem_Ico, Set.mem_ofPred_eq] at hp_ge ⊢
      push Not at hp_ge
      exact ⟨hp_ge, hp_neg⟩

/-- Jump operation: if p ∈ S and p + q ∉ S, then jump_{p,q}(S) = (S \ {p}) ∪ {p + q}. -/
def jump (S : State) (p : Level) (q : ℕ) (_hp : p ∈ S.levels)
    (_hpq : p + q ∉ S.levels) (_hq : q > 0) : State where
  levels := (S.levels \ {p}) ∪ {p + q}
  finite_nonneg := by
    apply Set.Finite.subset
    · exact S.finite_nonneg.union (Set.finite_singleton (p + q))
    · intro x ⟨hx_nonneg, hx_mem⟩
      simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx_mem ⊢
      cases hx_mem with
      | inl h => left; exact ⟨hx_nonneg, h.1⟩
      | inr h => right; exact h
  finite_negative_missing := by
    apply Set.Finite.subset
    · exact S.finite_negative_missing.union (Set.finite_singleton p)
    · intro x ⟨hx_neg, hx_nmem⟩
      simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx_nmem ⊢
      by_cases hxp : x = p
      · right; exact hxp
      · left
        constructor
        · exact hx_neg
        · intro hx_in_S
          apply hx_nmem
          left
          exact ⟨hx_in_S, hxp⟩

/-- A state S is reachable from T by a sequence of jumps. -/
inductive ReachableByJumps (T : State) : State → Prop where
  | refl : ReachableByJumps T T
  | step (S S' : State) (p : Level) (q : ℕ) (hp : p ∈ S.levels)
      (hpq : p + q ∉ S.levels) (hq : q > 0) :
      ReachableByJumps T S → S' = S.jump p q hp hpq hq → ReachableByJumps T S'

/-- A state S is reachable from T by a sequence of jumps with total jump amount m.
This is an extended version of `ReachableByJumps` that tracks the cumulative sum
of all jump sizes, which is needed to prove energy formulas. -/
inductive ReachableByJumpsWithTotal (T : State) : State → ℕ → Prop where
  | refl : ReachableByJumpsWithTotal T T 0
  | step (S S' : State) (p : Level) (q : ℕ) (m : ℕ) (hp : p ∈ S.levels)
      (hpq : p + q ∉ S.levels) (hq : q > 0) :
      ReachableByJumpsWithTotal T S m → S' = S.jump p q hp hpq hq →
      ReachableByJumpsWithTotal T S' (m + q)

/-- The explicit set of levels in an excited state E_{ℓ,μ}.
E_{ℓ,μ} = {p | p < ℓ-k} ∪ {ℓ-1-i+μ_i | i ∈ {0,...,k-1}}
where k is the number of parts and μ_i are the parts (sorted in decreasing order).

We use `mu.parts.sort (· ≥ ·)` to get a canonical decreasing ordering of parts.
This ensures that the excited levels uniquely encode the partition, since with sorted
parts the function `i ↦ parts[i] - i` is strictly decreasing (hence injective). -/
def excitedStateLevels (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) : Set Level :=
  let parts := mu.parts.sort (· ≥ ·)
  let k := parts.length
  {p : Level | p < ell - k} ∪
  {p : Level | ∃ i : Fin k, p = ell - 1 - i + parts.get (i.cast (by omega))}

/-- The excited state has finitely many nonnegative levels. -/
theorem excitedStateLevels_finite_nonneg (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) :
    Set.Finite {p : Level | p ≥ 0 ∧ p ∈ excitedStateLevels ell mu} := by
  unfold excitedStateLevels
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  let parts := mu.parts.sort (· ≥ ·)
  let k := parts.length
  -- The first set {p | p ≥ 0 ∧ p < ell - k} is finite
  have h1 : Set.Finite {p : Level | p ≥ 0 ∧ p < ell - k} :=
    Set.finite_Ico 0 (ell - k)
  -- The second set {p | ∃ i, p = ...} is finite (range of finite type)
  have h2 : Set.Finite {p : Level | ∃ i : Fin k, p = ell - 1 - i + parts.get (i.cast (by omega))} := by
    have : {p : Level | ∃ i : Fin k, p = ell - 1 - i + parts.get (i.cast (by omega))} ⊆
           Set.range (fun i : Fin k => ell - 1 - i + parts.get (i.cast (by omega))) := by
      intro p hp
      obtain ⟨i, hi⟩ := hp
      exact ⟨i, hi.symm⟩
    exact Set.Finite.subset (Set.finite_range _) this
  -- The target set is a subset of the union
  apply Set.Finite.subset (h1.union h2)
  intro p ⟨hp_nonneg, hp_mem⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  cases hp_mem with
  | inl h => left; exact ⟨hp_nonneg, h⟩
  | inr h => right; exact h

/-- The excited state has finitely many missing negative levels. -/
theorem excitedStateLevels_finite_negative_missing (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) :
    Set.Finite {p : Level | p < 0 ∧ p ∉ excitedStateLevels ell mu} := by
  -- A negative level p is missing if:
  -- 1. p ≥ ell - k (not in the unbounded part)
  -- 2. p is not one of the finitely many jumped levels
  -- The missing negative levels are a subset of {p | ell - k ≤ p < 0}
  apply Set.Finite.subset
  · exact Set.finite_Icc (ell - ↑((mu.parts.sort (· ≥ ·)).length)) (-1) |>.image (fun x => x)
  · intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    obtain ⟨hp_neg, hp_nmem⟩ := hp
    unfold excitedStateLevels at hp_nmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hp_nmem
    simp only [Set.mem_image, Set.mem_Icc]
    use p
    constructor
    · constructor
      · exact hp_nmem.1
      · linarith
    · rfl

/-- The excited state E_{ℓ,μ} obtained from the ground state by jumping electrons
according to the partition μ.

Given a partition μ = (μ₁, μ₂, ..., μₖ) of some n, we start with the ℓ-ground state
and let the k highest electrons jump by μ₁, μ₂, ..., μₖ steps respectively. -/
noncomputable def excitedState (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) : State where
  levels := excitedStateLevels ell mu
  finite_nonneg := excitedStateLevels_finite_nonneg ell mu
  finite_negative_missing := excitedStateLevels_finite_negative_missing ell mu

/-- The levels of an intermediate state after i jumps.
After i jumps, we have all levels below (ell - i), plus the i jump targets. -/
def intermediateStateLevels (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) : Set ℤ :=
  {p : ℤ | p < ell - i} ∪ 
  {p : ℤ | ∃ j : Fin i, p = ell - 1 - j + parts.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩}

/-- The intermediate state levels have finitely many nonnegative elements. -/
theorem intermediateStateLevels_finite_nonneg (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) :
    Set.Finite {p : ℤ | p ≥ 0 ∧ p ∈ intermediateStateLevels ell parts i hi} := by
  unfold intermediateStateLevels
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  have h1 : Set.Finite {p : ℤ | p ≥ 0 ∧ p < ell - i} := Set.finite_Ico 0 (ell - i)
  have h2 : Set.Finite {p : ℤ | ∃ j : Fin i, p = ell - 1 - j + parts.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩} := by
    apply Set.Finite.subset (Set.finite_range (fun j : Fin i => ell - 1 - j + parts.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩))
    intro p ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  apply Set.Finite.subset (h1.union h2)
  intro p ⟨hp_nonneg, hp_mem⟩
  cases hp_mem with
  | inl hp => left; exact ⟨hp_nonneg, hp⟩
  | inr hp => right; exact hp

/-- The intermediate state levels have finitely many negative missing elements. -/
theorem intermediateStateLevels_finite_neg_missing (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) :
    Set.Finite {p : ℤ | p < 0 ∧ p ∉ intermediateStateLevels ell parts i hi} := by
  unfold intermediateStateLevels
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt]
  apply Set.Finite.subset (Set.finite_Ico (ell - i) 0)
  intro p ⟨hp_neg, hp_ge, _⟩
  exact ⟨hp_ge, hp_neg⟩

/-- The intermediate state after i jumps. -/
noncomputable def intermediateState (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) : State where
  levels := intermediateStateLevels ell parts i hi
  finite_nonneg := intermediateStateLevels_finite_nonneg ell parts i hi
  finite_negative_missing := intermediateStateLevels_finite_neg_missing ell parts i hi

/-- The bijection Φ_ℓ : {partitions} → {states with particle number ℓ}.
Here we use Σ n, Nat.Partition n to represent all partitions. -/
noncomputable def partitionToState (ell : ℤ) : (Σ n, Nat.Partition n) → State :=
  fun ⟨_, mu⟩ => excitedState ell mu

/-- The base level of a state is the smallest level not in S.
This is well-defined because:
1. The set of levels not in S is nonempty (S can't contain all integers)
2. The set is bounded below (only finitely many negative levels are missing) -/
noncomputable def baseLevel (S : State) : ℤ :=
  sInf {p : ℤ | p ∉ S.levels}

/-- The excited levels of a state (levels in S that are ≥ baseLevel). -/
noncomputable def excitedLevelsSet (S : State) : Set ℤ :=
  S.levels ∩ {p | p ≥ baseLevel S}

/-- The excited levels form a finite set. -/
theorem excitedLevelsSet_finite (S : State) : Set.Finite (excitedLevelsSet S) := by
  unfold excitedLevelsSet
  by_cases h : baseLevel S ≥ 0
  · have hsub : S.levels ∩ {p | p ≥ baseLevel S} ⊆ {p | p ≥ 0 ∧ p ∈ S.levels} := by
      intro p ⟨hp_mem, hp_ge⟩; exact ⟨le_trans h hp_ge, hp_mem⟩
    exact Set.Finite.subset S.finite_nonneg hsub
  · push Not at h
    have h1 : S.levels ∩ {p | p ≥ baseLevel S} ⊆
              {p | p ≥ 0 ∧ p ∈ S.levels} ∪ Set.Ico (baseLevel S) 0 := by
      intro p ⟨hp_mem, hp_ge⟩
      by_cases hp_nonneg : p ≥ 0
      · left; exact ⟨hp_nonneg, hp_mem⟩
      · push Not at hp_nonneg; right; simp only [Set.mem_Ico]; exact ⟨hp_ge, hp_nonneg⟩
    apply Set.Finite.subset _ h1
    exact Set.Finite.union S.finite_nonneg (Set.finite_Ico (baseLevel S) 0)

/-- The excited levels as a finset. -/
noncomputable def excitedLevelsFinset (S : State) : Finset ℤ :=
  (excitedLevelsSet_finite S).toFinset

/-- The "partition size" of a state: the n such that energy(S) = |parnum(S)|² + 2n.

This is well-defined by energy_eq_parnum_sq_add_even and equals the size of the
unique partition μ with excitedState (parnum S) μ = S. -/
noncomputable def partitionSize (S : State) : ℕ :=
  (S.energy - S.parnum.natAbs ^ 2) / 2
/-! ### Bijection between (P, N) pairs and States

We establish a bijection between pairs (P, N) of finite subsets of ℕ and States.
- P represents the nonnegative levels in the state (n ∈ P means n ∈ S.levels)
- N represents the negative levels that are MISSING from the state
  (n ∈ N means -(n+1) ∉ S.levels, i.e., the negative level at position n is missing)

This bijection is key to proving `coeff_double_sum_eq_coeff_stateGenFun`.

**Key insight**: For a state S:
- The nonnegative levels in S form a finite set P ⊆ ℕ
- The negative levels missing from S can be indexed by a finite set N ⊆ ℕ
  where n ∈ N means the level -(n+1) is missing

Under this bijection:
- energy(S) = ∑_{n∈P}(2n+1) + ∑_{n∈N}(2n+1)
- parnum(S) = |P| - |N|

These formulas match the exponent and z-power in the double sum expansion of jacobiZZProduct.
-/


/-- Construct a state from a pair (P, N) of finite subsets of ℕ.
- P represents the nonnegative levels in the state (n ∈ P means n ∈ S.levels)
- N represents the negative levels that are MISSING from the state
  (n ∈ N means -(n+1) ∉ S.levels) -/
def fromFinsetPair (P N : Finset ℕ) : State where
  levels := {p : Level | (p ≥ 0 ∧ p.toNat ∈ P) ∨ (p < 0 ∧ ((-p - 1).toNat) ∉ N)}
  finite_nonneg := by
    have hP : Set.Finite ((fun n : ℕ => (n : ℤ)) '' (P : Set ℕ)) := P.finite_toSet.image _
    apply Set.Finite.subset hP
    intro p ⟨hp_nonneg, hp_in⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe] at hp_in ⊢
    rcases hp_in with ⟨_, hp_P⟩ | ⟨hp_neg, _⟩
    · use p.toNat, hp_P; exact Int.toNat_of_nonneg hp_nonneg
    · linarith
  finite_negative_missing := by
    have hN : Set.Finite ((fun n : ℕ => -(n : ℤ) - 1) '' (N : Set ℕ)) := N.finite_toSet.image _
    apply Set.Finite.subset hN
    intro p ⟨hp_neg, hp_nmem⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe] at hp_nmem ⊢
    push Not at hp_nmem
    have hp_N := hp_nmem.2 hp_neg
    have h : -p - 1 ≥ 0 := by linarith
    use (-p - 1).toNat
    exact ⟨hp_N, by simp only [Int.toNat_of_nonneg h]; ring⟩

/-- Extract the P component (nonnegative levels) from a state.
For a state S, this returns {n ∈ ℕ : n ∈ S.levels}. -/
noncomputable def toP (S : State) : Finset ℕ :=
  S.finite_nonneg.toFinset.image (fun p => p.toNat)

/-- Extract the N component (missing negative levels) from a state.
For a state S, this returns {n ∈ ℕ : -(n+1) ∉ S.levels}. -/
noncomputable def toN (S : State) : Finset ℕ :=
  S.finite_negative_missing.toFinset.image (fun p => (-p - 1).toNat)

end State
section BijectionLemma

open State

end BijectionLemma

end Jacobi
/-! ## Alternative Proof Approach: Evaluation Homomorphism

This section provides infrastructure for an alternative proof of `jacobi_triple_product`
that bypasses the file ordering issue in `jacobiLHS_mul_partitionGenFun`.

The idea is to derive `jacobi_triple_product` from `jacobi_triple_product_fps'` 
(which is fully proved later in this file) by constructing an evaluation map from 
`JacobiRing` to `ℚ⟦X⟧` that sends `q^e * z^ℓ` to `u^e * v^ℓ * X^{ae + bℓ}`.

If we can show:
1. `evalJacobi jacobiLHS' = jacobiLHSEval a b u v`
2. `evalJacobi jacobiRHS' = jacobiRHSEval a b u v`

Then `jacobi_triple_product` follows immediately from `jacobi_triple_product_fps'`.

Note: The original analysis was tracked in issue 9a9b6a12 (now resolved and split into
issues 62191a41 and 9dd5829e for focused tracking of the remaining blockers).
-/


section EvalJacobi

/-- Evaluation of a Laurent polynomial coefficient at z = v·X^b.
For c ∈ LaurentPolynomial ℤ, evaluate at z = v·X^b to get an element of ℚ⟦X⟧.
This sends T^ℓ → v^ℓ·X^{bℓ} when bℓ ≥ 0 for all ℓ in the support of c. -/
noncomputable def evalLaurentCoeff (b : ℤ) (v : ℚ) (c : LaurentPolynomial ℤ) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  c.coeff.support.sum fun ℓ => ((c.coeff ℓ : ℚ) * v^ℓ) • PowerSeries.X ^ (b * ℓ).toNat

/-- Full evaluation map from JacobiRing to ℚ⟦X⟧.
Sends a power series f = ∑_e c_e · q^e (where c_e ∈ LaurentPolynomial ℤ)
to ∑_e evalLaurentCoeff(c_e) · u^e · X^{ae}.

This is well-defined when:
- a > 0 (ensures exponents ae are nonnegative for e ≥ 0)
- a ≥ |b| (ensures exponents ae + bℓ are nonnegative for all ℓ in supports)
-/
noncomputable def evalJacobi (a b : ℤ) (u v : ℚ) (f : JacobiRing) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  -- For each coefficient c_e of q^e in f, evaluate c_e at z = v·X^b,
  -- then multiply by u^e and shift by X^{ae}
  ∑' e : ℕ, (u^e : ℚ) • evalLaurentCoeff b v (PowerSeries.coeff e f) * PowerSeries.X ^ (a * e).toNat
/-! ### Corrected evaluation infrastructure

The original `evalJacobi` has a bug: it computes `X^{ae} · X^{(bℓ).toNat}` instead of 
`X^{(ae + bℓ).toNat}`. These differ when `bℓ < 0` but `ae + bℓ ≥ 0`.

We fix this by defining `evalJacobiCorrect` that computes the combined exponent directly.
-/


/-- Evaluation of a Laurent polynomial coefficient with a shift parameter.
For c ∈ LaurentPolynomial ℤ and shift e, evaluate at z = v·X^b with base exponent a·e.
This sends T^ℓ → v^ℓ·X^{(a·e + b·ℓ).toNat}, computing the combined exponent correctly. -/
noncomputable def evalLaurentCoeffShifted (a b : ℤ) (v : ℚ) (e : ℕ) (c : LaurentPolynomial ℤ) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  c.coeff.support.sum fun ℓ => ((c.coeff ℓ : ℚ) * v^ℓ) • PowerSeries.X ^ (a * e + b * ℓ).toNat

/-- Corrected full evaluation map from JacobiRing to ℚ⟦X⟧.
This version computes the combined exponent (a·e + b·ℓ).toNat correctly,
avoiding the truncation issue in the original evalJacobi. -/
noncomputable def evalJacobiCorrect (a b : ℤ) (u v : ℚ) (f : JacobiRing) : ℚ⟦X⟧ :=
  letI : TopologicalSpace ℚ := ⊥
  haveI : DiscreteTopology ℚ := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := ℚ)
  ∑' e : ℕ, (u^e : ℚ) • evalLaurentCoeffShifted a b v e (PowerSeries.coeff e f)
/-! ### Roadmap for completing jacobi_triple_product via evaluation

The alternative proof approach uses `jacobi_triple_product_fps'` (proved later in this file)
which shows `jacobiLHS' = jacobiRHS'` in `JacobiRing = PowerSeries (LaurentPolynomial ℤ)`.

To derive `jacobi_triple_product` (the evaluated form), we need:

1. **evalJacobiCorrect_jacobiRHS'**: `evalJacobiCorrect a b u v jacobiRHS' = jacobiRHSEval a b u v`
   
   Proof sketch:
   - `jacobiRHS' = ∑' ℓ, jacobiSumTerm ℓ` where `jacobiSumTerm ℓ = X^{ℓ²} · C(T^ℓ)`
   - The coefficient of `q^{ℓ²}` in `jacobiSumTerm ℓ` is `T^ℓ`
   - By `evalLaurentCoeffShifted_T`: evaluation gives `v^ℓ · X^{(aℓ² + bℓ).toNat}`
   - So `evalJacobiCorrect` of `jacobiSumTerm ℓ` is `u^{ℓ²} · v^ℓ · X^{(aℓ² + bℓ).toNat}`
   - Summing over ℓ gives `jacobiRHSEval`

2. **evalJacobiCorrect_jacobiLHS'**: `evalJacobiCorrect a b u v jacobiLHS' = jacobiLHSEval a b u v`
   
   This is more complex because `jacobiLHS'` is an infinite product.
   Proof sketch:
   - `jacobiLHS' = ∏' n, jacobiProductTerm n`
   - Each `jacobiProductTerm n` involves factors `(1 + X^{2n-1} · C(T^1))`, etc.
   - The evaluation preserves products (needs ring homomorphism property)
   - Each factor evaluates to the corresponding factor in `jacobiLHSEval`

3. **jacobi_triple_product_via_evalCorrect**: Alternative proof using evaluation
   ```
   jacobiLHSEval = evalJacobiCorrect jacobiLHS'   -- by evalJacobiCorrect_jacobiLHS'
                 = evalJacobiCorrect jacobiRHS'   -- by jacobi_triple_product_fps'
                 = jacobiRHSEval                  -- by evalJacobiCorrect_jacobiRHS'
   ```

**Current status**: Corrected infrastructure added. The key lemmas need to be proved.
-/

-- Note: evalJacobiCorrect_jacobiLHS' is defined in the MovedLemmas section at the end of the file,
-- after jacobi_triple_product_fps' which it depends on. See the MovedLemmas section for the proof.

end EvalJacobi
/-! ### Bijection Infrastructure for Coefficient Equality

These lemmas establish the key bijection argument for proving
`coeff_double_sum_eq_coeff_stateGenFun`. Both sums can be reindexed to sums
over states with a given energy, and the value at each state is T(parnum(S)).
-/


/-- The set of states with a given energy is finite. -/
def statesWithEnergy (d : ℕ) : Set State := {S : State | S.energy = d}
/-! ### State Generating Function Infrastructure

The key to proving Jacobi's triple product identity is the "state generating function":
  ∑_{S state} q^{energy(S)} z^{parnum(S)}

Both the LHS and RHS of the identity, when multiplied by the partition generating function
∏_{k>0} (1-q^{2k})^{-1}, equal this state generating function.

For the RHS:
  RHS · ∏_{k>0} (1-q^{2k})^{-1} = ∑_{ℓ∈ℤ} q^{ℓ²} z^ℓ · ∑_{μ partition} q^{2|μ|}
                                = ∑_{ℓ∈ℤ} ∑_{μ partition} q^{ℓ² + 2|μ|} z^ℓ

By the bijection partitionToState_bijective, this equals:
  ∑_{S state} q^{energy(S)} z^{parnum(S)}

since energy(E_{ℓ,μ}) = ℓ² + 2|μ| and parnum(E_{ℓ,μ}) = ℓ.

For the LHS:
  LHS · ∏_{k>0} (1-q^{2k})^{-1} = ∏_{k>0}((1+q^{2k-1}z)(1+q^{2k-1}z^{-1}))

Using binary expansion, this product equals:
  ∑_{P,N finite} q^{∑_{p∈P}(2p-1) + ∑_{n∈N}(2n-1)} z^{|P| - |N|}

which is exactly the state generating function.
-/
/-! ## Lemma for Substitution -/
/-! ## Transfer from ℚ to ℤ for Euler's Pentagonal Number Theorem

The proof of Euler's pentagonal number theorem proceeds by:
1. Proving the identity over ℚ using Jacobi's triple product
2. Transferring from ℚ to ℤ using the fact that both sides have integer coefficients

The key lemma `eulerProduct_coeff_map` shows that the coefficients of `eulerProduct`
are compatible with the ring homomorphism ℤ → ℚ.
-/
/-! ## Connecting Lemmas for Euler's Pentagonal Number Theorem

These lemmas connect `jacobiLHSEval` and `jacobiRHSEval` at the specific parameters
(a=3, b=1, u=1, v=-1) to `eulerProduct` and `pentagonalSeries` respectively.
Together with `jacobi_triple_product` and `fps_eq_of_sq_eq`, they complete the proof
of Euler's pentagonal number theorem.
-/
/-! ## Euler's Pentagonal Number Theorem (Main Result) -/
/-! ## Euler's Recursion for Sum of Divisors -/


section EulerSumDivisors

open scoped ArithmeticFunction.sigma

/-- The sum of divisors generating function: S = ∑_{k>0} σ(k) x^k.
This is the generating function for the sum of divisors function σ₁. -/
noncomputable def sigmaSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (σ 1 n : ℤ)
/-! ### Helper Lemmas for the Partition-Sigma Identity -/

end EulerSumDivisors
/-! ### Additional Infrastructure for Jacobi Triple Product

The following lemmas provide additional infrastructure for the proof of
`jacobi_triple_product_fps'`. They establish key coefficient properties
for both the LHS and RHS of the identity.
-/


section JacobiCoefficients

end JacobiCoefficients
/-! ### Moved Lemmas: coeff_double_sum_eq_coeff_stateGenFun and dependencies

These lemmas were moved here from earlier in the file because they depend on
the State infrastructure and `finsetPair_sum_eq_partition_sum`.
-/


section MovedLemmas


end MovedLemmas

end AlgebraicCombinatorics
