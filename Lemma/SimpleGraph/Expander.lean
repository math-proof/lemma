import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Expander
open SimpleGraph


namespace SimpleGraph

/--
[mem_externalNeighborSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma mem_externalNeighborSet
  {G : SimpleGraph V}
  {A : Set V}
  {v : V} :
-- imply
  v ∈ G.externalNeighborSet A ↔ v ∉ A ∧ ∃ a ∈ A, G.Adj a v :=
-- proof
  Iff.rfl

end SimpleGraph

namespace SimpleGraph

/--
[externalNeighborSet_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma externalNeighborSet_disjoint
  {G : SimpleGraph V}
  {A : Set V} :
-- imply
  Disjoint (G.externalNeighborSet A) A := by
-- proof
  rw [Set.disjoint_left]
  intro v hv hA
  exact hv.1 hA

end SimpleGraph

namespace SimpleGraph

/--
[exists_adj_of_mem_externalNeighborSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma exists_adj_of_mem_externalNeighborSet
  {G : SimpleGraph V}
  {A : Set V}
  {v : V}
-- given
  (h : v ∈ G.externalNeighborSet A) :
-- imply
  ∃ a ∈ A, G.Adj a v :=
-- proof
  h.2

end SimpleGraph

namespace SimpleGraph

/--
[IsCExpander.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma IsCExpander.pos
  [Finite V]
  {G : SimpleGraph V}
  {C : ℝ}
-- given
  (h : G.IsCExpander C) :
-- imply
  0 < C :=
-- proof
  h.1

end SimpleGraph

namespace SimpleGraph

/--
[IsCExpander.small_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma IsCExpander.small_expansion
  [Finite V]
  {G : SimpleGraph V}
  {C : ℝ}
  {A : Set V}
-- given
  (h : G.IsCExpander C)
  (hA : (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C)) :
-- imply
  C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ) :=
-- proof
  h.2.1 A hA

end SimpleGraph

namespace SimpleGraph

/--
[IsCExpander.large_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma IsCExpander.large_edge
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
  ∃ a ∈ A, ∃ b ∈ B, G.Adj a b :=
-- proof
  h.2.2 A B hdis hA hB

end SimpleGraph

namespace SimpleGraph

/--
[IsUniformVertexExpander.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma IsUniformVertexExpander.pos
  [Finite V]
  {G : SimpleGraph V}
  {h : ℝ}
-- given
  (hh : G.IsUniformVertexExpander h) :
-- imply
  0 < h :=
-- proof
  hh.1

end SimpleGraph

namespace SimpleGraph

/--
[IsUniformVertexExpander.small_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
lemma IsUniformVertexExpander.small_expansion
  [Finite V]
  {G : SimpleGraph V}
  {h : ℝ}
  {S : Set V}
-- given
  (hh : G.IsUniformVertexExpander h)
  (hS : (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2) :
-- imply
  h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ) :=
-- proof
  hh.2 S hS

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
