/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Factor.lean -/

import Mathlib.Data.Finite.Prod
import Mathlib.Data.List.OfFn
/-!
# Factors of right-infinite words

This file represents a right-infinite word over `α` as a function `ℕ → α` and defines its
fixed-length factors and initial segments. This representation follows
[Blackman--Kristensen--Northey, arXiv:2306.09853v3](https://arxiv.org/abs/2306.09853v3).
The definitions of `factor`, `factorSet`, and `finite_factorSet` adapt corresponding CC0
definitions from
[`rwst/Confinement-Certificates`](https://github.com/rwst/Confinement-Certificates), revision
`eb810d8f86e49b2b8e058d02a9edac9e5fedafc8`, in
`ForMathlib/Combinatorics/SubwordComplexity.lean` and
`ForMathlib/Combinatorics/InfiniteComplexity.lean`.

The nonempty list-valued factor predicate follows the substring convention in
[Short--Stanier--van Son--Zabolotskii, arXiv:2608.13199v1](https://arxiv.org/abs/2608.13199v1),
line 562, where a substring is indexed by endpoints `r ≤ s` and is therefore nonempty.
The unqualified `IsFactor` additionally follows the conventional empty-allowed
definition and agrees with membership in `factorSet` at every length.

## Main definitions

* `InfiniteWord.factor` — the length-`k` consecutive block at position `i`.
* `InfiniteWord.factorSet` — the set of all length-`k` factors.
* `InfiniteWord.initial` — the initial length-`k` block.
* `InfiniteWord.factorList` — a list-valued version of `factor`.
* `InfiniteWord.IsFactor` — the assertion that a list occurs in an infinite word.
* `InfiniteWord.IsNonemptyFactor` — the source's nonempty substring convention.
-/


namespace InfiniteWord

variable {α : Type*}

/-- The length-`k` factor of a right-infinite word `u` at position `i`. -/
def factor (u : ℕ → α) (k i : ℕ) : Fin k → α := fun s => u (i + s)

/-- The set of length-`k` factors occurring in `u`. -/
def factorSet (u : ℕ → α) (k : ℕ) : Set (Fin k → α) :=
  Set.range (factor u k)

/-- The length-`k` initial segment of a right-infinite word `u`. -/
def initial (u : ℕ → α) (k : ℕ) : Fin k → α :=
  factor u k 0

/-- The list-valued length-`k` factor of `u` at position `i`. -/
def factorList (u : ℕ → α) (k i : ℕ) : List α :=
  List.ofFn (factor u k i)

/-- A finite list occurs as a contiguous factor of a right-infinite word. -/
def IsFactor (w : List α) (u : ℕ → α) : Prop :=
  ∃ i, factorList u w.length i = w

/-- A nonempty finite list occurs as a contiguous factor of a right-infinite word,
using the endpoint convention of the cited source. -/
def IsNonemptyFactor (w : List α) (u : ℕ → α) : Prop :=
  w ≠ [] ∧ ∃ i, ∀ j (hj : j < w.length), w[j]'hj = u (i + j)

end InfiniteWord
