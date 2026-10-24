/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# Skip Two Indices in Fin

This file provides the `Fin.skipTwo` function which maps `Fin n` to `Fin (n+2)` by skipping
two specified indices.

## Main definitions

* `Fin.skipTwo i j hij` - Given `i < j` in `Fin (n+2)`, produces a function `Fin n → Fin (n+2)`
  that skips both `i` and `j`

## Main results

* `Fin.skipTwo_injective` - `skipTwo` is injective
* `Fin.skipTwo_strictMono` - `skipTwo` is strictly monotone
* `Fin.skipTwo_range` - The range of `skipTwo i j` is exactly `{i, j}ᶜ`
* `Fin.skipTwo_ne_first` - `skipTwo i j k ≠ i` for all `k`
* `Fin.skipTwo_ne_second` - `skipTwo i j k ≠ j` for all `k`
* `Fin.skipTwo_inverse` - Every element not equal to `i` or `j` is in the range

## Implementation notes

This module provides the canonical location for the `Fin.skipTwo` definition and its
API lemmas. Files that need `skipTwo` functionality (such as `DesnanotJacobi.lean`)
import this module and may define local abbreviations for convenience.

## References

The `skipTwo` function is the natural generalization of `Fin.succAbove` (which skips one index)
to skipping two indices. It arises in:
- Desnanot-Jacobi identity proofs (removing two rows/columns from a matrix)
- Pfaffian computations (perfect matching induction)
- Tiling decompositions (removing boundary elements)
-/


namespace Fin

/-- Remove two elements from `Fin (n+2)` to get `Fin n`.
    Given `i < j` in `Fin (n+2)`, we map `Fin n` to `Fin (n+2)` by skipping `i` and `j`.

    The function is defined piecewise:
    - If `k < i`, then `skipTwo i j k = k`
    - If `i ≤ k` and `k + 1 < j`, then `skipTwo i j k = k + 1`
    - If `k + 1 ≥ j`, then `skipTwo i j k = k + 2` -/
def skipTwo {n : ℕ} (i j : Fin (n + 2)) (_hij : i < j) : Fin n → Fin (n + 2) :=
  fun k =>
    if (k : ℕ) < i then ⟨k, by omega⟩
    else if (k : ℕ) + 1 < j then ⟨k + 1, by omega⟩
    else ⟨k + 2, by omega⟩

end Fin
