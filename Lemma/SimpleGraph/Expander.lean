import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Expander
open SimpleGraph


/--
[mem_externalNeighborSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma mem_externalNeighborSet_eq
  {G : SimpleGraph V}
  {A : Set V}
  {v : V} :
-- imply
  v ∈ G.externalNeighborSet A ↔ v ∉ A ∧ ∃ a ∈ A, G.Adj a v := by
-- proof
  apply SimpleGraph.mem_externalNeighborSet G A v

/--
[externalNeighborSet_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma externalNeighborSet_disjoint_eq
  {G : SimpleGraph V}
  {A : Set V} :
-- imply
  Disjoint (G.externalNeighborSet A) A := by
-- proof
  apply SimpleGraph.externalNeighborSet_disjoint G A

/--
[exists_adj_of_mem_externalNeighborSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma exists_adj_of_mem_externalNeighborSet_eq
  {G : SimpleGraph V}
  {A : Set V}
  {v : V}
-- given
  (h : v ∈ G.externalNeighborSet A) :
-- imply
  ∃ a ∈ A, G.Adj a v := by
-- proof
  apply SimpleGraph.exists_adj_of_mem_externalNeighborSet G h

/--
[IsCExpander.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma IsCExpander_pos_eq
  [Finite V]
  {G : SimpleGraph V}
  {C : ℝ}
-- given
  (h : G.IsCExpander C) :
-- imply
  0 < C := by
-- proof
  apply SimpleGraph.IsCExpander.pos G h

/--
[IsCExpander.small_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma IsCExpander_small_expansion_eq
  [Finite V]
  {G : SimpleGraph V}
  {C : ℝ}
  {A : Set V}
-- given
  (h : G.IsCExpander C)
  (hA : (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C)) :
-- imply
  C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ) := by
-- proof
  apply SimpleGraph.IsCExpander.small_expansion G h A hA

/--
[IsCExpander.large_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma IsCExpander_large_edge_eq
  [Finite V]
  {G : SimpleGraph V}
  {C : ℝ}
  {A B : Set V}
-- given
  (h : G.IsCExpander C)
  (hdis : Disjoint A B)
  (hA : (Nat.card V : ℝ) / (2 * C) ≤ (A.ncard : ℝ))
  (hB : (Nat.card V : ℝ) / (2 * C) ≤ (B.ncard : ℝ)) :
-- imply
  ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
-- proof
  apply SimpleGraph.IsCExpander.large_edge G h A B hdis hA hB

/--
[IsUniformVertexExpander.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma IsUniformVertexExpander_pos_eq
  [Finite V]
  {G : SimpleGraph V}
  {h : ℝ}
-- given
  (hh : G.IsUniformVertexExpander h) :
-- imply
  0 < h := by
-- proof
  apply SimpleGraph.IsUniformVertexExpander.pos G hh

/--
[IsUniformVertexExpander.small_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma IsUniformVertexExpander_small_expansion_eq
  [Finite V]
  {G : SimpleGraph V}
  {h : ℝ}
  {S : Set V}
-- given
  (hh : G.IsUniformVertexExpander h)
  (hS : (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2) :
-- imply
  h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ) := by
-- proof
  apply SimpleGraph.IsUniformVertexExpander.small_expansion G hh S hS


-- created on 2026-10-20
