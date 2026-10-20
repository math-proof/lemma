/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean -/

import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Deza graphs

This module introduces Deza graphs with parameters `(n, k, b, a)`,
following Golubyatnikov (see https://arxiv.org/abs/2608.13089v1, lines 163--164).
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A Deza graph with parameters `(n, k, b, a)`, after Golubyatnikov
(see https://arxiv.org/abs/2608.13089v1, lines 163--164): exactly `n` vertices,
`k`-regular, with the common-neighbour count of any two distinct vertices equal
to `a` or to `b`, independently of adjacency. -/
structure IsDezaWith (n k b a : ℕ) : Prop where
  /-- Lower parameter inequality `a ≤ b`. -/
  a_le_b : a ≤ b
  /-- Middle parameter inequality `b ≤ k`. -/
  b_le_k : b ≤ k
  /-- Strict parameter inequality `k < n`. -/
  k_lt_n : k < n
  /-- Exactly `n` vertices. -/
  card_eq : Fintype.card V = n
  /-- `k`-regularity. -/
  regular : G.IsRegularOfDegree k
  /-- Two-valued common-neighbour counts. -/
  common_eq : ∀ u v : V, u ≠ v →
    Fintype.card (G.commonNeighbors u v) = a ∨
      Fintype.card (G.commonNeighbors u v) = b

/-- The chained bound `a ≤ k`. -/
theorem IsDezaWith.a_le_k {n k b a : ℕ} (h : G.IsDezaWith n k b a) : a ≤ k :=
  le_trans h.a_le_b h.b_le_k

/-- The chained bound `b < n`. -/
theorem IsDezaWith.b_lt_n {n k b a : ℕ} (h : G.IsDezaWith n k b a) : b < n :=
  lt_of_le_of_lt h.b_le_k h.k_lt_n

/-- The chained bound `a < n`. -/
theorem IsDezaWith.a_lt_n {n k b a : ℕ} (h : G.IsDezaWith n k b a) : a < n :=
  lt_of_le_of_lt h.a_le_k h.k_lt_n

end SimpleGraph
