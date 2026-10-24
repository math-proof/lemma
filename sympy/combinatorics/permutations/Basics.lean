/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
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


open Equiv Function Finset

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

-- Verify that the symmetric group is indeed a group (def.perm.perm (b))
example {X : Type*} : Group (Equiv.Perm X) := inferInstance

/-- `S_n` is a finite group. -/
instance sn_fintype (n : ℕ) : Fintype (Sn n) := inferInstance

/-- `S_n` has decidable equality. -/
instance sn_decidableEq (n : ℕ) : DecidableEq (Sn n) := inferInstance
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
/-! ## Transpositions (def.perm.tij)

A transposition `t_{i,j}` swaps `i` and `j` and fixes all other elements.

From the textbook (def.perm.tij):
> Let `i` and `j` be two distinct elements of a set `X`. Then, the transposition `t_{i,j}` is
> the permutation of `X` that sends `i` to `j`, sends `j` to `i`, and leaves all other
> elements of `X` unchanged.

In Mathlib, this is `Equiv.swap i j`. -/


/-- The transposition swapping `i` and `j`. In Mathlib, this is `Equiv.swap i j`.
    (def.perm.tij)

    A transposition `t_{i,j}` is the permutation of `X` that:
    - sends `i` to `j` (see `transposition_apply_left`)
    - sends `j` to `i` (see `transposition_apply_right`)
    - leaves all other elements unchanged (see `transposition_apply_of_ne_of_ne`) -/
abbrev transposition {X : Type*} [DecidableEq X] (i j : X) : Equiv.Perm X := Equiv.swap i j

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

/-- Notation for simple transposition. -/
scoped notation "s[" i "]" => simpleTransposition i
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

/-- A permutation is a cycle if any two non-fixed points are related by repeated
    application of the permutation. -/
abbrev IsCycle {X : Type*} (σ : Equiv.Perm X) : Prop := Equiv.Perm.IsCycle σ

/-- The support of a cycle (the set of elements it moves). -/
abbrev cycleSupport {X : Type*} [DecidableEq X] [Fintype X] (σ : Equiv.Perm X) : Finset X :=
  σ.support
/-! ## Counting k-cycles (exe.perm.cyc.how-many-kcyc)

The number of k-cycles in `S_n` (for k > 1) is `n(n-1)...(n-k+1)/k = C(n,k) * (k-1)!`. -/
/-! ## Involutions (def.perm.invol)

An involution is a permutation equal to its own inverse. -/


/-- A permutation is an involution if `σ ∘ σ = id`. (def.perm.invol)

From the textbook:
> An *involution* of X means a map f: X → X that satisfies f ∘ f = id.
> Clearly, an involution is always a permutation, and equals its own inverse.

Equivalent characterizations:
- `IsInvolution σ ↔ σ * σ = 1` (definition)
- `IsInvolution σ ↔ σ⁻¹ = σ` (see `isInvolution_iff_eq_inv`)
- `IsInvolution σ ↔ Function.Involutive σ` (see `isInvolution_iff_involutive`)
- `IsInvolution σ ↔ ∀ x, σ (σ x) = x` (see `isInvolution_iff_forall`)
-/
def IsInvolution {X : Type*} (σ : Equiv.Perm X) : Prop := σ * σ = 1

/-- Decidable instance for IsInvolution on finite types. -/
instance instDecidableIsInvolution {X : Type*} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) : Decidable (IsInvolution σ) :=
  inferInstanceAs (Decidable (σ * σ = 1))

end AlgebraicCombinatorics
