/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Real.Basic
/-!
# `C`-expanders

Formalizes Definition 1 of Michael Krivelevich, Alan Lew, and Peleg Michaeli,
*Rigidity of expanders and pseudorandom graphs*,
https://arxiv.org/abs/2608.21058v1.

For `C > 0`, an `n`-vertex graph is a `C`-expander when every small vertex set
expands by a factor `C` and any two large disjoint vertex sets have an edge
between them.
-/


namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- External neighbourhood of `A`: vertices outside `A` adjacent to some vertex of `A`. -/
def externalNeighborSet (A : Set V) : Set V :=
  { v | v ∉ A ∧ ∃ a ∈ A, G.Adj a v }

/-- Definition 1 from the source: `C`-expander with a real parameter `C`. -/
def IsCExpander [Finite V] (C : ℝ) : Prop :=
  0 < C ∧
    (∀ A : Set V, (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C) →
      C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ)) ∧
    ∀ A B : Set V, Disjoint A B →
      (Nat.card V : ℝ) / (2 * C) ≤ (A.ncard : ℝ) →
      (Nat.card V : ℝ) / (2 * C) ≤ (B.ncard : ℝ) →
      ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- Uniform vertex expansion: every vertex set `S` with `|S| ≤ |V| / 2`
has at least `h * |S|` neighbours outside `S`. -/
def IsUniformVertexExpander [Finite V] (h : ℝ) : Prop :=
  0 < h ∧
    ∀ S : Set V, (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2 →
      h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ)

end SimpleGraph
