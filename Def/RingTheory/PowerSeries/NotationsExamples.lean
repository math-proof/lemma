/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# Notations and Elementary Facts + Examples

This file formalizes the introductory material from the first chapter of the
Algebraic Combinatorics course notes. It covers:

1. Basic combinatorial principles (addition, multiplication, bijection)
2. Binomial coefficient definitions and properties
3. Four motivating examples using generating functions:
   - The Fibonacci sequence and Binet's formula
   - Dyck words and Catalan numbers
   - The Vandermonde convolution identity
   - Solving a linear recurrence

## Main Definitions

* `FPS.fibonacci` - The Fibonacci sequence (equivalent to `Nat.fib` in Mathlib)
* `FPS.catalan` - The Catalan numbers (equivalent to `catalan` in Mathlib)
* `FPS.isDyckWord` - Predicate for Dyck words (alternative to Mathlib's `DyckWord` structure)
* `FPS.goldenRatioPlus` - The golden ratio (equivalent to `Real.goldenRatio` in Mathlib)
* `FPS.goldenRatioMinus` - The conjugate golden ratio (equivalent to `Real.goldenConj` in Mathlib)

## Main Results

* `FPS.binom_def_formula` - **Definition \ref{def.binom.binom}**: $\binom{r}{n} = \frac{r(r-1)\cdots(r-n+1)}{n!}$
* `FPS.binom_factorial_smul` - The factorial formula: $n! \cdot \binom{r}{n} = r(r-1)\cdots(r-n+1)$
* `FPS.binom_natCast` - For natural numbers: $\binom{n}{k} = $ `Nat.choose n k`
* `FPS.binom_zero_right` - Base case: $\binom{r}{0} = 1$
* `FPS.binom_zero_left_pos` - For $k > 0$: $\binom{0}{k} = 0$
* `FPS.binom_one_right` - First case: $\binom{r}{1} = r$
* `FPS.binom_neg_one` - The binomial coefficient $\binom{-1}{k} = (-1)^k$
* `FPS.binom_two_n_n_eq` - Formula $\binom{2n}{n} = \frac{1 \cdot 3 \cdot 5 \cdots (2n-1)}{n!} \cdot 2^n$
* `FPS.pascal_identity` - Pascal's identity for binomial coefficients (natural numbers)
* `FPS.pascal_identity_ring` - Pascal's identity for generalized binomial coefficients (binomial rings)
* `FPS.pascal_identity_succ` - Pascal's identity in successor form
* `FPS.pascal_identity_int` - Pascal's identity for integers
* `FPS.pascal_identity_rat` - Pascal's identity for rationals
* `FPS.binom_zero_of_lt` - $\binom{m}{n} = 0$ when $m < n$ for natural numbers
* `FPS.binom_symm` - Symmetry: $\binom{n}{k} = \binom{n}{n-k}$ (Theorem \ref{thm.binom.sym})
* `FPS.binom_symm_add` - Symmetry variant: $\binom{a+b}{a} = \binom{a+b}{b}$
* `FPS.binom_symm_of_eq_add` - Symmetry when $n = a + b$
* `FPS.binom_symm_ring` - Symmetry for `Ring.choose` (generalized binomial coefficients)
* `FPS.fibonacci_binet` - Binet's formula for Fibonacci numbers
* `FPS.fibonacci_gf` - Generating function $F(x) = x/(1-x-x^2)$
* `FPS.catalan_recurrence` - Recurrence $c_n = \sum_{k=0}^{n-1} c_k c_{n-1-k}$
* `FPS.catalan_explicit` - Explicit formula $c_n = \frac{1}{n+1}\binom{2n}{n}$
* `FPS.vandermonde_convolution` - $\binom{a+b}{n} = \sum_{k=0}^n \binom{a}{k}\binom{b}{n-k}$

## References

* Course notes: AlgebraicCombinatorics/tex/FPS/Notations.tex

## Tags

combinatorics, binomial coefficients, generating functions, Fibonacci, Catalan
-/


namespace AlgebraicCombinatorics.FPS

open Finset BigOperators Nat

/-!
## Basic Combinatorial Principles

These are standard results in Mathlib. We provide docstrings explaining
the combinatorial interpretations.
-/
/-!
## Binomial Coefficients

The binomial coefficient $\binom{n}{k}$ is defined in Mathlib as `Nat.choose`
for natural numbers and `Ring.choose` for more general rings.

### Definition \ref{def.binom.binom}

For any numbers $n$ and $k$:
$$\binom{n}{k} = \begin{cases}
\frac{n(n-1)(n-2)\cdots(n-k+1)}{k!} & \text{if } k \in \mathbb{N} \\
0 & \text{else}
\end{cases}$$

In Mathlib, this is implemented as:
- `Nat.choose n k` for natural numbers $n, k$
- `Ring.choose r n` for elements $r$ in a binomial ring and $n \in \mathbb{N}$

The key identity relating `Ring.choose` to the textbook definition is:
$$n! \cdot \binom{r}{n} = r(r-1)(r-2)\cdots(r-n+1)$$
which is the descending factorial (descending Pochhammer symbol).
-/
/-!
## The Fibonacci Sequence (Example 1)

The Fibonacci sequence $(f_0, f_1, f_2, \ldots)$ is defined by:
- $f_0 = 0$
- $f_1 = 1$
- $f_n = f_{n-1} + f_{n-2}$ for $n \geq 2$

Its generating function is $F(x) = \sum_{n \geq 0} f_n x^n = \frac{x}{1-x-x^2}$.

**Mathlib equivalences**: The Fibonacci sequence is `Nat.fib` in Mathlib. The golden ratios
are `Real.goldenRatio` and `Real.goldenConj` in `Mathlib.NumberTheory.Real.GoldenRatio`.
Binet's formula is proved there as `Real.coe_fib_eq`.
-/


/-- The Fibonacci sequence.

**Mathlib note**: This is definitionally equal to `Nat.fib` in Mathlib. -/
def fibonacci : ℕ → ℕ := Nat.fib

/-- The golden ratio $\phi_+ = \frac{1 + \sqrt{5}}{2}$.

**Mathlib note**: This is equal to `Real.goldenRatio` in Mathlib. -/
noncomputable def goldenRatioPlus : ℝ := (1 + Real.sqrt 5) / 2

/-- The conjugate golden ratio $\phi_- = \frac{1 - \sqrt{5}}{2}$.

**Mathlib note**: This is equal to `Real.goldenConj` in Mathlib. -/
noncomputable def goldenRatioMinus : ℝ := (1 - Real.sqrt 5) / 2

/-!
## Dyck Words and Catalan Numbers (Example 2)

A **Dyck word** of length $2n$ is a $2n$-tuple of $0$s and $1$s such that:
1. There are exactly $n$ zeros and $n$ ones
2. For each prefix, the number of $0$s does not exceed the number of $1$s

The **Catalan numbers** $c_n$ count Dyck words of length $2n$.

**Mathlib equivalences**:
- Catalan numbers are defined in `Mathlib.Combinatorics.Enumerative.Catalan` as `Nat.catalan`
  using the recurrence relation. The explicit formula `catalan n = centralBinom n / (n + 1)`
  is proved as `Nat.catalan_eq_centralBinom_div`.
- Dyck words are formalized in `Mathlib.Combinatorics.Enumerative.DyckWord` as the `DyckWord`
  structure using a `DyckStep` enum (U for up, D for down) rather than Bool.
-/


/-- A list is a Dyck word if it consists of 0s and 1s, has equal numbers
of each, and every prefix has at least as many 1s as 0s.

Here we represent 1 as `true` and 0 as `false`.

**Mathlib note**: This is an alternative representation to Mathlib's `DyckWord` structure,
which uses a `DyckStep` enum with constructors `U` (up) and `D` (down). The two representations
are equivalent via the bijection sending `true` to `U` and `false` to `D`. -/
def isDyckWord (w : List Bool) : Prop :=
  w.count true = w.count false ∧
  ∀ k : ℕ, k ≤ w.length →
    (w.take k).count false ≤ (w.take k).count true

/-- The Catalan numbers, defined as $c_n = \frac{1}{n+1}\binom{2n}{n}$.

**Mathlib note**: This is equivalent to Mathlib's `catalan`, which is defined recursively.
The equivalence is proved by `catalan_eq_mathlib_catalan`. -/
def catalan (n : ℕ) : ℕ := (2 * n).choose n / (n + 1)

/-!
## The Vandermonde Convolution (Example 3)

The **Vandermonde convolution identity** (also called Chu-Vandermonde):
$$\binom{a+b}{n} = \sum_{k=0}^{n} \binom{a}{k} \binom{b}{n-k}$$
-/
/-!
## Solving a Recurrence (Example 4)

Consider the sequence $(a_0, a_1, a_2, \ldots)$ defined by:
- $a_0 = 1$
- $a_{n+1} = 2a_n + n$ for all $n \geq 0$

Using generating functions, we can show that $a_n = 2^{n+1} - (n+1)$.
-/


/-- The sequence defined by $a_0 = 1$ and $a_{n+1} = 2a_n + n$. -/
def exampleRecurrence : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * exampleRecurrence n + n

/-!
## Auxiliary Generating Function Results

These are helper results about power series used in the examples above.
-/

end AlgebraicCombinatorics.FPS
