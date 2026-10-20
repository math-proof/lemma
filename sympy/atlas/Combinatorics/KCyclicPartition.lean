/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/KCyclicPartition.lean -/

import Mathlib.GroupTheory.Perm.Cycle.Type

namespace MetaMathlibExt

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Truncated-cycle successor for a permutation `σ` at label `i`.

It characterizes the exact evaluation `σ^(i)(i) = j` as the first positive
forward iterate `(σ ^ m) i` whose label is `≤ i`: there exists `m > 0` with
`(σ ^ m) i = j`, `j ≤ i`, and every earlier positive iterate has label `> i`. -/
def TruncatedSucc (σ : Equiv.Perm V) (i j : V) : Prop :=
  ∃ m : ℕ, 0 < m ∧ j ≤ i ∧ (σ ^ m) i = j ∧
    ∀ m' : ℕ, 0 < m' → m' < m → i < (σ ^ m') i

/-- `k`-cyclic partition of a labeled graph.

`σ` is a permutation of `V` whose total number of cycles, counting fixed points
via `σ.cycleType.card + (Fintype.card V - σ.support.card)`, equals `k`, and for
every vertex `i`, the exact truncated-cycle successor `σ^(i)(i) = j` implies
there is no directed edge from `i` to `j`.

Source: JIS statement `jis_758fa72fca5bb19057a27c73` in Gonzales,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Gonzales/gonzales2.tex>, lines 345–346,
SHA-256 `2d78a778c999aa0af889445a63ee690bb3a5d3ac741b6beb0b777654e1f4a627`. -/
def IsKCyclicPartition (σ : Equiv.Perm V) (edge : V → V → Prop) (k : ℕ) : Prop :=
  σ.cycleType.card + (Fintype.card V - σ.support.card) = k ∧
    ∀ i j : V, TruncatedSucc σ i j → ¬ edge i j

end MetaMathlibExt
