/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Instance.GroupTheory.Perm.Basics
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

/-! ### Composition notation (def.perm.perm (c))

In the textbook, `αβ` denotes the composition `α ∘ β`, which sends `x` to `α(β(x))`.
In Mathlib, this is the group multiplication `α * β`. -/
/-! ### Powers of permutations (def.perm.perm (d))

The i-th power `α^i` is defined for any integer `i`. -/
/-! ## Conjugation isomorphism (prop.perm.Sf)

If `f : X ≃ Y` is a bijection, then the map `σ ↦ f ∘ σ ∘ f⁻¹` is a group isomorphism
from `S_X` to `S_Y`. -/


/-- Given a bijection `f : X ≃ Y`, conjugation by `f` gives a group isomorphism
    from `Perm X` to `Perm Y`. (prop.perm.Sf)

    For each permutation `σ` of `X`, the map `f ∘ σ ∘ f⁻¹ : Y → Y` is a permutation of `Y`.
    Furthermore, the map `S_f : S_X → S_Y, σ ↦ f ∘ σ ∘ f⁻¹` is a group isomorphism. -/
def symmetricGroup_conj_iso {X Y : Type*} (f : X ≃ Y) : Equiv.Perm X ≃* Equiv.Perm Y :=
  f.permCongrHom

/-! ## Permutation notations (def.perm.notations)

This section formalizes Definition `def.perm.notations` from the textbook, which introduces
three notations for representing permutations:

**(a)** A *two-line notation* of σ is a 2×n-array where the top row contains elements of [n]
in some order, and the bottom row contains their images under σ.

**(b)** The *one-line notation* (OLN) of σ is the n-tuple (σ(1), σ(2), ..., σ(n)).

**(c)** The *cycle digraph* of σ is a directed graph with vertices 1, 2, ..., n and
arcs i → σ(i) for all i ∈ [n].

In Lean, we formalize these as follows:
- Two-line notation: a function that maps each element to its image (essentially the permutation itself)
- One-line notation: a `Fin n → Fin n` function, or equivalently a `Vector (Fin n) n`
- Cycle digraph: a `SimpleGraph` with edges determined by the permutation
-/
/-! ### Two-line notation (def.perm.notations (a))

A two-line notation of σ ∈ S_n is a 2×n-array where:
- The top row contains the elements p₁, p₂, ..., pₙ of [n] in some order
- The bottom row contains σ(p₁), σ(p₂), ..., σ(pₙ)

The most common form uses pᵢ = i, giving the array:
  ⎛ 1      2      ...  n    ⎞
  ⎝ σ(1)  σ(2)  ...  σ(n)  ⎠

In Lean, a permutation σ : Equiv.Perm (Fin n) already encodes this information:
the "two-line notation" is essentially the graph of σ as a function. -/


/-- The two-line notation of a permutation σ ∈ S_n, represented as a list of pairs
    [(1, σ(1)), (2, σ(2)), ..., (n, σ(n))].

    This corresponds to the standard two-line notation:
      ⎛ 1      2      ...  n    ⎞
      ⎝ σ(1)  σ(2)  ...  σ(n)  ⎠

    (def.perm.notations (a)) -/
def twoLineNotation {n : ℕ} (σ : Sn n) : List (Fin n × Fin n) :=
  (List.finRange n).map (fun i => (i, σ i))

/-! ### One-line notation (def.perm.notations (b))

The one-line notation (OLN) of σ ∈ S_n is the n-tuple (σ(1), σ(2), ..., σ(n)).

In Lean, a permutation σ : Sn n = Equiv.Perm (Fin n) is already essentially its OLN,
since we can evaluate σ at any index. We provide explicit conversions. -/


/-- The one-line notation of a permutation σ ∈ S_n, as a list [σ(0), σ(1), ..., σ(n-1)].

    Note: We use 0-indexing (Fin n starts at 0), so this is [σ(0), σ(1), ..., σ(n-1)]
    rather than [σ(1), σ(2), ..., σ(n)] as in the textbook.

    (def.perm.notations (b)) -/
def oneLineNotation {n : ℕ} (σ : Sn n) : List (Fin n) :=
  (List.finRange n).map σ

/-- Convert a list to a permutation, if it's a valid one-line notation.
    Returns the permutation represented by the list. -/
noncomputable def oneLineNotationToPerm {n : ℕ} (l : List (Fin n)) (hl : l.length = n) (hnodup : l.Nodup) :
    Sn n :=
  Equiv.ofBijective (fun i => l[i.val]'(by omega)) ⟨by
    intro i j hij
    have hi' : i.val < l.length := by omega
    have hj' : j.val < l.length := by omega
    have hinj := List.Nodup.getElem_inj_iff hnodup (hi := hi') (hj := hj')
    simp only [Fin.ext_iff]
    exact hinj.mp hij, by
    intro y
    have hy : y ∈ l := by
      have hcard : l.toFinset.card = n := by
        rw [List.toFinset_card_of_nodup hnodup, hl]
      have hfull : l.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        simp [hcard]
      rw [← List.mem_toFinset, hfull]
      exact Finset.mem_univ y
    obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
    exact ⟨⟨i, by omega⟩, hiy⟩⟩

/-! ### Cycle digraph (def.perm.notations (c))

The cycle digraph of σ ∈ S_n is a directed graph with:
- Vertices: 1, 2, ..., n (or 0, 1, ..., n-1 in 0-indexed form)
- Arcs: i → σ(i) for all i ∈ [n]

In Lean, we represent this as a `SimpleGraph` where there's an edge between i and j
iff σ(i) = j (and i ≠ j to avoid self-loops in the SimpleGraph sense).

Note: The cycle digraph is naturally a directed graph, but for simplicity we can also
consider the underlying undirected graph structure. -/


/-- The cycle digraph of a permutation σ, as an undirected simple graph.

    There is an edge between i and j iff σ(i) = j or σ(j) = i (and i ≠ j).
    This captures the "orbit structure" of the permutation.

    (def.perm.notations (c)) -/
def cycleDigraph {n : ℕ} (σ : Sn n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (σ i = j ∨ σ j = i)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ ⟨hn, _⟩ => hn rfl⟩

end AlgebraicCombinatorics
