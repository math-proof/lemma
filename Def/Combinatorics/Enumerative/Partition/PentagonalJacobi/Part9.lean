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
import Theorem.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part5
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

namespace State

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

end EulerSumDivisors
end AlgebraicCombinatorics
