/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.IntegerCompositions.Part13
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

/-- The geometric series identity: `(∑_{i=0}^{p-1} x^i) * (1 - x) = 1 - x^p`. -/
theorem geom_series_mul_one_sub (p : ℕ) : 
    (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) * (1 - PowerSeries.X) = 
    1 - PowerSeries.X ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_range_succ, add_mul, ih]
    ring

/-- Power of `invOneSubPow`: `(invOneSubPow ℤ 1)^k = invOneSubPow ℤ k`. -/
theorem invOneSubPow_pow (k : ℕ) : (PowerSeries.invOneSubPow ℤ 1) ^ k = PowerSeries.invOneSubPow ℤ k := by
  induction k with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ k ih =>
    rw [pow_succ, ih, mul_comm, ← PowerSeries.invOneSubPow_add]
    ring_nf

/-- The geometric series equals `(1 - X^p) * (1 - X)^{-1}`. -/
theorem geom_series_eq_mul_inv (p : ℕ) : 
    (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i) = 
    (1 - PowerSeries.X ^ p) * (PowerSeries.invOneSubPow ℤ 1).val := by
  have h1 : (PowerSeries.invOneSubPow ℤ 1).val = PowerSeries.mk 1 := by
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp only [PowerSeries.coeff_mk, Nat.choose_zero_right, Pi.one_apply, Nat.cast_one]
  rw [h1]
  have h2 : (1 - PowerSeries.X) * PowerSeries.mk 1 = (1 : PowerSeries ℤ) := by
    rw [mul_comm]; exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  have h3 := geom_series_mul_one_sub p
  calc ∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i 
      = (∑ i ∈ range p, PowerSeries.X ^ i) * 1 := by ring
    _ = (∑ i ∈ range p, PowerSeries.X ^ i) * ((1 - PowerSeries.X) * PowerSeries.mk 1) := by rw [h2]
    _ = ((∑ i ∈ range p, PowerSeries.X ^ i) * (1 - PowerSeries.X)) * PowerSeries.mk 1 := by ring
    _ = (1 - PowerSeries.X ^ p) * PowerSeries.mk 1 := by rw [h3]

/-- The generating function equals `(1-X^p)^k * (1-X)^{-k}`. -/
theorem genFun_eq (k p : ℕ) :
    genFun k p = (1 - PowerSeries.X ^ p) ^ k * (PowerSeries.invOneSubPow ℤ k).val := by
  unfold genFun
  rw [geom_series_eq_mul_inv]
  rw [mul_pow]
  congr 1
  have h1 : (PowerSeries.invOneSubPow ℤ 1).val ^ k = ((PowerSeries.invOneSubPow ℤ 1) ^ k).val := by
    simp only [Units.val_pow_eq_pow_val]
  have h2 : (PowerSeries.invOneSubPow ℤ 1) ^ k = PowerSeries.invOneSubPow ℤ k := invOneSubPow_pow k
  rw [h1, h2]

/-- The coefficient of `x^n` in `(1-x)^{-k}` for `k > 0`. -/
theorem coeff_invOneSubPow (k n : ℕ) (hk : 0 < k) :
    (PowerSeries.invOneSubPow ℤ k).val.coeff n = Nat.choose (k - 1 + n) (k - 1) := by
  have := @PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ _ k hk
  rw [this]
  simp only [PowerSeries.coeff_mk]

/-- Coefficient of the geometric series `∑_{i<p} x^i` at `x^m`. -/
theorem coeff_geom_series (p m : ℕ) :
    (∑ i ∈ range p, (PowerSeries.X : PowerSeries ℤ) ^ i).coeff m = if m < p then 1 else 0 := by
  simp only [map_sum, PowerSeries.coeff_X_pow]
  rw [sum_ite_eq]
  simp [mem_range]

end BoundedWeakComposition
end AlgebraicCombinatorics
