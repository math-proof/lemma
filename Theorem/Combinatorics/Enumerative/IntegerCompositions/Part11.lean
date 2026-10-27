/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.IntegerCompositions.Part16
open Finset Nat BigOperators
set_option allowUnsafeReducibility true
attribute [local reducible] PNat

/-!
# Integer Compositions

This file formalizes integer compositions and weak compositions, following
Section sec.fps.intcomps of the source text.

## Main definitions

* `Composition` - A composition as a `List ℕ+` (tuple of positive integers)
* `Composition.append` - Concatenation of two compositions
* `Composition.ofSize n` - The subtype of compositions with size `n`
* `Composition.ofSizeIntoParts n k` - The subtype of compositions with size `n` and length `k`
* `WeakComposition` - A weak composition as a `List ℕ` (tuple of nonnegative integers)
* `WeakComposition.ofSizeIntoParts n k` - Weak compositions of `n` into `k` parts
* `BoundedWeakComposition n k p` - Weak compositions with entries in `{0, 1, ..., p-1}`

## Main results

* `Composition.card_ofSizeIntoParts_pos` - The number of compositions of `n` into `k` parts
  is `Nat.choose (n-1) (k-1)` for `n > 0` and `k > 0` (Theorem thm.fps.comps.num-comps-n-k)
* `Composition.card_ofSizeIntoParts_zero` - The number of compositions of `0` into `k` parts
  is `1` if `k = 0`, else `0`
* `Composition.card_ofSizeIntoParts_k_zero` - The number of compositions of `n > 0` into
  `0` parts is `0`
* `Composition.card_ofSize` - The number of compositions of `n` is `2^(n-1)` for `n > 0`
  (Theorem thm.fps.comps.num-comps-n)
* `WeakComposition.card_ofSizeIntoParts` - The number of weak compositions of `n` into `k` parts
  is `Nat.choose (n+k-1) n` (Theorem thm.fps.comps.num-wcomps-n-k)
* `BoundedWeakComposition.card` - The number of weak compositions with bounded entries
  (Theorem thm.fps.comps.num-wpcomps-n-k)
* `binom_sum_identity` - An identity involving binomial coefficients
  (Proposition prop.fps.comps.num-w2comps-n-k-id)

## Implementation notes

This file defines `Composition` as `List ℕ+`, which is an alternative representation to
Mathlib's `Mathlib.Combinatorics.Enumerative.Composition` which uses `Composition n` as a
structure with `blocks : List ℕ` and proofs of positivity and sum. Both representations
are equivalent; we use `List ℕ+` here to follow the source text's presentation more directly.

## References

See the source LaTeX file `AlgebraicCombinatorics/tex/FPS/IntegerCompositions.tex`
-/


namespace AlgebraicCombinatorics

namespace BoundedWeakComposition

/-- The cardinality of bounded antidiagonals equals the cardinality of BoundedWeakComposition. -/
theorem card_boundedAntidiag_eq (n k p : ℕ) :
    (boundedAntidiag n k p).card = Fintype.card (BoundedWeakComposition n k p) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_eq.mpr ⟨bwcEquiv n k p⟩

/-- 
Key lemma: the coefficient of `x^n` in the generating function equals the count.

This is the standard fact that `[x^n](∑_{i<p} x^i)^k` counts k-tuples in `{0,...,p-1}^k` summing to `n`.
The proof uses the product rule for power series coefficients.
-/
theorem coeff_genFun (n k p : ℕ) :
    (genFun k p).coeff n = Fintype.card (BoundedWeakComposition n k p) := by
  unfold genFun
  rw [PowerSeries.coeff_pow]
  simp only [coeff_geom_series]
  -- The product is 1 iff all l i < p, else 0
  have h_prod : ∀ l : ℕ →₀ ℕ, (∏ i ∈ range k, (if l i < p then (1 : ℤ) else 0)) = 
      if ∀ i ∈ range k, l i < p then 1 else 0 := by
    intro l
    split_ifs with h
    · exact prod_eq_one (fun i hi => by simp [h i hi])
    · push Not at h
      obtain ⟨i, hi, hli⟩ := h
      exact prod_eq_zero hi (by simp [hli])
  simp_rw [h_prod]
  rw [sum_ite, sum_const_zero, add_zero, sum_const]
  simp only [nsmul_eq_mul, mul_one]
  -- Now: (filter (...) (finsuppAntidiag (range k) n)).card = Fintype.card (BoundedWeakComposition n k p)
  rw [show ({x ∈ (range k).finsuppAntidiag n | ∀ i ∈ range k, x i < p} : Finset (ℕ →₀ ℕ)) = 
       boundedAntidiag n k p from rfl]
  rw [card_boundedAntidiag_eq]

/-- 
The main coefficient extraction using the generating function approach.

Using `genFun k p = (1 - X^p)^k * (1-X)^{-k}` and the convolution formula:
- `(1-X^p)^k` has coefficient `(-1)^j C(k,j)` at `x^{pj}` for `j ≤ k`, else `0`
- `(1-X)^{-k}` has coefficient `C(k-1+m, k-1)` at `x^m` for `k > 0`

Convolving gives: `[x^n] = ∑_{pj ≤ n} (-1)^j C(k,j) * C(k-1+(n-pj), k-1)`
-/
-- The binomial expansion of (1 - X^p)^k
theorem one_sub_X_pow_pow_eq (p k : ℕ) : 
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ p) ^ k = 
    ∑ j ∈ range (k + 1), PowerSeries.C ((-1 : ℤ) ^ j * (Nat.choose k j : ℤ)) * (PowerSeries.X : PowerSeries ℤ) ^ (p * j) := by
  conv_lhs => rw [sub_eq_add_neg, add_comm, add_pow]
  simp only [one_pow, mul_one]
  congr 1 with j
  have h1 : (-(PowerSeries.X : PowerSeries ℤ) ^ p) ^ j = (-1)^j * (PowerSeries.X ^ p)^j := by
    rw [neg_pow]
  rw [h1, pow_mul]
  congr 1
  calc ((-1 : PowerSeries ℤ) ^ j * (PowerSeries.X ^ p) ^ j * ↑(k.choose j) : PowerSeries ℤ)
      = (PowerSeries.X ^ p) ^ j * ((-1 : PowerSeries ℤ) ^ j * ↑(k.choose j)) := by ring
    _ = (PowerSeries.X ^ p) ^ j * PowerSeries.C ((-1 : ℤ) ^ j * ↑(k.choose j)) := by
        congr 1
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    _ = PowerSeries.C ((-1 : ℤ) ^ j * ↑(k.choose j)) * (PowerSeries.X ^ p) ^ j := by ring

-- Coefficient of X^n in (1 - X^p)^k
theorem coeff_one_sub_X_pow_pow (p k n : ℕ) :
    PowerSeries.coeff (R := ℤ) n ((1 - PowerSeries.X ^ p) ^ k) = 
      ∑ j ∈ (range (k + 1)).filter (fun j => p * j = n),
        (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) := by
  rw [one_sub_X_pow_pow_eq]
  rw [map_sum]
  have h : ∀ j, (PowerSeries.coeff n) (PowerSeries.C ((-1 : ℤ) ^ j * (↑(k.choose j) : ℤ)) * (PowerSeries.X : PowerSeries ℤ) ^ (p * j)) = 
      if p * j = n then (-1 : ℤ)^j * (↑(k.choose j) : ℤ) else 0 := by
    intro j
    rw [PowerSeries.coeff_C_mul]
    simp only [PowerSeries.coeff_X_pow]
    split_ifs with h1 h2
    · ring
    · omega
    · omega
    · ring
  simp_rw [h]
  rw [sum_filter]

-- Helper lemma for binomial coefficient symmetry
theorem choose_symm_helper (n k : ℕ) (hk : 0 < k) : 
    (k - 1 + n).choose (k - 1) = (n + k - 1).choose n := by
  have h1 : k - 1 + n = n + (k - 1) := by omega
  have h2 : n + (k - 1) = n + k - 1 := by omega
  rw [h1, h2]
  have h3 : n + k - 1 = n + (k - 1) := by omega
  rw [h3]
  rw [Nat.choose_symm_add]

theorem coeff_genFun_formula (n k p : ℕ) :
    (genFun k p).coeff n = 
      ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n),
        (-1 : ℤ) ^ j * (Nat.choose k j) * (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
  rw [genFun_eq, sum_filter]
  -- Handle the case k = 0 separately
  by_cases hk : k = 0
  · subst hk
    rw [pow_zero, one_mul, PowerSeries.invOneSubPow_zero, Units.val_one, PowerSeries.coeff_one]
    simp only [Nat.add_zero]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ite_false]
      have : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos
      simp [Nat.choose_eq_zero_of_lt this]
  -- Now k > 0
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  -- Use the convolution formula
  rw [PowerSeries.coeff_mul]
  -- Transform the antidiagonal sum
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (f := fun m r => 
    (PowerSeries.coeff m) ((1 - PowerSeries.X ^ p) ^ k) * 
    (PowerSeries.coeff r) (PowerSeries.invOneSubPow ℤ k).val)]
  -- Expand the coefficient of (1-X^p)^k
  simp_rw [coeff_one_sub_X_pow_pow]
  -- Distribute the multiplication
  simp_rw [sum_mul]
  -- Swap the order of summation
  simp_rw [sum_filter]
  rw [sum_comm]
  -- Simplify using sum_ite_eq'
  conv_lhs =>
    arg 2
    ext j
    simp only [eq_comm (a := p * j)]
    rw [sum_ite_eq' (range (n + 1)) (p * j)]
    simp only [mem_range]
  -- Convert p * j < n + 1 to p * j ≤ n
  simp_rw [show ∀ j, p * j < n + 1 ↔ p * j ≤ n by intro j; omega]
  -- Apply sum_congr to match the terms
  apply sum_congr rfl
  intro j _
  split_ifs with h
  -- Case: p * j ≤ n
  rw [coeff_invOneSubPow k (n - p * j) hk_pos]
  have h_choose : (k - 1 + (n - p * j)).choose (k - 1) = (n - p * j + k - 1).choose (n - p * j) := by
    rw [choose_symm_helper (n - p * j) k hk_pos]
  rw [h_choose]; ring

/--
**Theorem thm.fps.comps.num-wpcomps-n-k**:
The number of `k`-tuples `(α₁, α₂, ..., αₖ) ∈ {0, 1, ..., p-1}^k`
satisfying `α₁ + α₂ + ... + αₖ = n` is
`∑_{j : p*j ≤ n} (-1)^j * C(k,j) * C(n - p*j + k - 1, n - p*j)`.

Note: The sum is restricted to `j` with `p * j ≤ n` because when `p * j > n`,
the mathematical binomial coefficient `C(n - p*j + k - 1, n - p*j)` should be 0
(as there are no compositions with negative sum), but `Nat.choose` with truncating
subtraction would give a non-zero value.

## Proof Strategy

The proof uses generating functions. The generating function for bounded weak compositions
is `W_{k,p} = (∑_{i=0}^{p-1} x^i)^k`, which equals `((1-x^p)/(1-x))^k = (1-x^p)^k * (1-x)^{-k}`.

Using binomial expansions:
- `(1-x^p)^k = ∑_{j=0}^k (-1)^j C(k,j) x^{pj}`
- `(1-x)^{-k} = ∑_{m≥0} C(m+k-1, m) x^m`

Convolving these gives the formula.
-/
theorem card (n k p : ℕ) :
    (Fintype.card (BoundedWeakComposition n k p) : ℤ) =
      ∑ j ∈ (range (k + 1)).filter (fun j => p * j ≤ n),
        (-1 : ℤ) ^ j * (Nat.choose k j) * (Nat.choose (n - p * j + k - 1) (n - p * j)) := by
  rw [← coeff_genFun]
  exact coeff_genFun_formula n k p

end BoundedWeakComposition

/-! ### Binary Strings Identity -/


/-- For f : Fin k → Fin 2, the sum of values equals the cardinality of the support (positions with value 1). -/
theorem sum_fin2_eq_card_support (k : ℕ) (f : Fin k → Fin 2) :
    ∑ i, (f i).val = (Finset.univ.filter (fun i => f i = 1)).card := by
  conv_lhs =>
    arg 2
    ext i
    rw [show (f i).val = if f i = 1 then 1 else 0 by
      rcases f i with ⟨v, hv⟩
      interval_cases v <;> simp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]

/-- Elements of Fin 2 are either 0 or 1. -/
theorem fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v <;> simp

end AlgebraicCombinatorics
