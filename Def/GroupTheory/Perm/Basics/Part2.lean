/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Abbrev.GroupTheory.Perm.Basics.Part2
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

/-- Extract a canonical pair from a swap. -/
noncomputable def swapToPair {X : Type*} [DecidableEq X] (σ : Equiv.Perm X) (hσ : σ.IsSwap) : X × X :=
  let x := Classical.choose hσ
  let hx := Classical.choose_spec hσ
  let y := Classical.choose hx
  (x, y)

/-! ## Simple transpositions (def.perm.si)

The simple transposition `s_i` swaps `i` and `i+1`. -/


/-- The simple transposition `s_i` swaps `i` and `i+1` in `Fin n`.
    Here `i : Fin (n - 1)` ensures `i+1 < n`.
    (def.perm.si)
    
    **This is the canonical definition** for simple transpositions in the codebase.
    
    **Equivalent definition in Inversions2.lean:**
    `Equiv.Perm.simpleTransposition` in `Inversions2.lean` defines the same permutation
    using a slightly different construction (with `castSucc`/`succ`). The equivalence is
    proven by `Equiv.Perm.simpleTransposition_eq_canonical`.
    
    See the equivalence lemmas `simpleTransposition_eq_swap_*` below for other formulations. -/
def simpleTransposition {n : ℕ} (i : Fin (n - 1)) : Sn n :=
  Equiv.swap ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
             ⟨i.val + 1, by omega⟩

end AlgebraicCombinatorics
