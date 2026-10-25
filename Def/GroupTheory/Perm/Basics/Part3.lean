/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Notation.GroupTheory.Perm.Basics
open Equiv Function Finset

/-!
# Basic definitions, transpositions, cycles and involutions

This file formalizes the basic definitions of permutations, transpositions, cycles,
and involutions from the Algebraic Combinatorics textbook.

## Main definitions

* `Equiv.Perm`: The type of permutations of a set (from Mathlib)
* `Equiv.swap`: The transposition swapping two elements (from Mathlib)
* `cyc`: The k-cycle `cyc_{i₁, i₂, ..., iₖ}` that cyclically permutes elements (def.perm.cycs)
* `Equiv.Perm.IsCycle`: Predicate for a permutation being a cycle (from Mathlib)
* `simpleTransposition`: The simple transposition swapping `i` and `i+1`
* `IsInvolution`: Predicate for a permutation being an involution

## Main results

* `symmetricGroup_card`: The symmetric group has `n!` elements
* `symmetricGroup_conj_iso`: Bijections induce isomorphisms of symmetric groups
* `transposition_apply_left`: `t_{i,j}(i) = j` (def.perm.tij)
* `transposition_apply_right`: `t_{i,j}(j) = i` (def.perm.tij)
* `transposition_apply_of_ne_of_ne`: `t_{i,j}(x) = x` for `x ≠ i, j` (def.perm.tij)
* `transposition_symm`: Transpositions are symmetric: `t_{i,j} = t_{j,i}`
* `transposition_sq_eq_one`: Transpositions are involutions: `t_{i,j}² = id`
* `num_transpositions`: The number of transpositions in S_X is C(|X|, 2)
* `simpleTransposition_eq_transposition`: `s_i = t_{i,i+1}` (def.perm.si)
* `simpleTransposition_apply_self`: `s_i(i) = i+1` (def.perm.si)
* `simpleTransposition_apply_succ`: `s_i(i+1) = i` (def.perm.si)
* `simpleTransposition_apply_of_ne`: `s_i(k) = k` for `k ≠ i, i+1` (def.perm.si)
* `simpleTransposition_support`: support of `s_i` is `{i, i+1}` (def.perm.si)
* `simpleTransposition_isSwap`: `s_i` is a swap (def.perm.si)
* `simpleTransposition_isCycle`: `s_i` is a 2-cycle (def.perm.si)
* `simpleTransposition_sq_eq_one`: Simple transpositions satisfy `s_i² = id`
* `simpleTransposition_comm`: Simple transpositions commute when `|i-j| > 1`
* `simpleTransposition_braid`: The braid relation `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}`
* `cyc_pair`: 2-cycles are exactly transpositions: `cyc [i, j] = swap i j`
* `cyc_rotate`: Cyclic rotation doesn't change the cycle
* `cyc_apply_getElem`: The cycle sends `l[j]` to `l[(j+1) % l.length]`
* `cycle_eq_transposition`: 2-cycles are exactly transpositions
* `num_kCycles_formula`: The number of k-cycles in `S_n` is `C(n,k) * (k-1)!`

## References

See `AlgebraicCombinatorics/tex/Permutations/Basics.tex` for the LaTeX source.

## Design note: simpleTransposition duplication

The `simpleTransposition` function is defined in this file (`AlgebraicCombinatorics.simpleTransposition`)
and also in `Inversions2.lean` (`Equiv.Perm.simpleTransposition`). Both definitions produce the same
permutation (proven by `Equiv.Perm.simpleTransposition_eq_canonical`).

**Which to use:**
- Use `AlgebraicCombinatorics.simpleTransposition` (this file) for basic properties of simple
  transpositions as swaps/cycles
- Use `Equiv.Perm.simpleTransposition` (Inversions2.lean) when working with reduced words,
  length functions, and Coxeter-style arguments

## Tags

permutation, symmetric group, transposition, cycle, involution
-/


namespace AlgebraicCombinatorics

/-! ## Properties of simple transpositions (prop.perm.si.rules) -/
/-! ### Equivalence lemmas for simpleTransposition

The `simpleTransposition` function is the **canonical definition** for the simple transposition
`s_i` that swaps `i` and `i+1` in `Fin n`. Other files may define local versions with slightly
different signatures. These lemmas establish the equivalence between formulations.

**Alternative formulations in the codebase:**
1. `Equiv.Perm.simpleTransposition` in `Inversions2.lean` - uses `castSucc`/`succ` pattern
2. `simpleTransposition` in `SymmetricFunctions/Definitions.lean` - uses `Nat.lt_of_lt_pred`
3. `simpleTransposition` in `SchurBasics.lean` - takes `Fin N` with explicit proof `hk : k.val + 1 < N`

All these definitions compute the same permutation: `Equiv.swap k (k+1)`.
-/
/-! ## Cycles (def.perm.cycs)

A k-cycle is a permutation that cyclically permutes k elements and fixes all others.

The textbook defines `cyc_{i₁, i₂, ..., iₖ}` as the permutation that sends
- `i₁ ↦ i₂`
- `i₂ ↦ i₃`
- ...
- `iₖ₋₁ ↦ iₖ`
- `iₖ ↦ i₁`
and fixes all other elements.

In Mathlib, this is `List.formPerm`. The predicate `Equiv.Perm.IsCycle` captures
when a permutation is a cycle. -/


/-- The k-cycle `cyc_{i₁, i₂, ..., iₖ}` is the permutation that sends
    `i₁ ↦ i₂ ↦ i₃ ↦ ... ↦ iₖ ↦ i₁` and fixes all other elements.
    (def.perm.cycs)
    
    This is the constructive definition from the textbook. In Mathlib,
    this is `List.formPerm`. -/
def cyc {X : Type*} [DecidableEq X] (l : List X) : Equiv.Perm X := l.formPerm

end AlgebraicCombinatorics
