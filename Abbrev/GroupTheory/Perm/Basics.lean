/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
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

/-! ## Basic definitions (def.perm.perm)

This section formalizes Definition `def.perm.perm` from the textbook:

**(a)** A *permutation* of X means a bijection from X to X.
In Mathlib, this is `Equiv.Perm X := X ≃ X`.

**(b)** The set of all permutations of X is a group under composition, called the
*symmetric group* of X, denoted `S_X`. Its neutral element is `id_X`, and its size is `|X|!`.
In Mathlib, `Equiv.Perm X` has a `Group` instance automatically.

**(c)** We write `αβ` for composition `α ∘ β` when `α, β ∈ S_X`. This sends each `x ∈ X`
to `α(β(x))`. In Mathlib, `(α * β) x = α (β x)`.

**(d)** If `α ∈ S_X` and `i ∈ ℤ`, then `α^i` denotes the i-th power of α in the group S_X.
- `α^i = α ∘ α ∘ ⋯ ∘ α` (i times) if `i ≥ 0`
- `α^0 = id_X`
- `α^(-1)` is the inverse of α

-/


/-- A permutation of a type `X` is a bijection from `X` to itself. (def.perm.perm (a))

In Mathlib, this is `Equiv.Perm X := X ≃ X`, i.e., the type of equivalences from `X` to `X`. -/
abbrev Permutation (X : Type*) := Equiv.Perm X

/-- The symmetric group of a type `X` is the group of all permutations of `X`.
    (def.perm.perm (b))

    In Mathlib, this is `Equiv.Perm X` with its natural `Group` instance. -/
abbrev SymmetricGroup (X : Type*) := Equiv.Perm X

/-! ### The n-th symmetric group (def.perm.Sn-iven)

In the textbook, `[n]` denotes the set `{1, 2, ..., n}`, which is an n-element set
for n ≥ 0 and empty for n ≤ 0.

In Lean/Mathlib, we use `Fin n = {0, 1, ..., n-1}` instead, which is also an n-element
set. This is a standard convention difference (0-indexed vs 1-indexed), but the
symmetric groups are isomorphic since both are n-element sets.

The symmetric group `S_[n]` (denoted `S_n`) is the group of all permutations of `[n]`.
Its size is `n!` when n ≥ 0. -/


/-- The set `[n]` from the textbook is represented by `Fin n` in Lean.

In the textbook (def.perm.Sn-iven), `[n]` denotes `{1, 2, ..., n}`.
In Lean, `Fin n` represents `{0, 1, ..., n-1}`.

Both are n-element sets for n ≥ 0, so their symmetric groups are isomorphic.
We use `Fin n` as it is the standard representation in Mathlib. -/
abbrev bracketN (n : ℕ) := Fin n

/-- The n-th symmetric group `S_n` is the group of permutations of `[n]`.
    (def.perm.Sn-iven)

In the textbook, `S_n` is defined as `S_[n]`, the symmetric group of `[n] = {1, 2, ..., n}`.
In Lean, we represent this as `Equiv.Perm (Fin n)`, the group of permutations of
`Fin n = {0, 1, ..., n-1}`.

The size of `S_n` is `n!` (see `sn_card`). -/
abbrev Sn (n : ℕ) := Equiv.Perm (Fin n)

end AlgebraicCombinatorics
