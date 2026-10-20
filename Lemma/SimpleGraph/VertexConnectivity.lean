import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
open SimpleGraph


/--
[isVertexConnected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma isVertexConnected_iff_eq
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V} :
-- imply
  G.IsVertexConnected k ↔
    k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected := by
-- proof
  apply SimpleGraph.isVertexConnected_iff

/--
[IsVertexConnected.card_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma IsVertexConnected_card_gt_eq
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
-- given
  (hG : G.IsVertexConnected k) :
-- imply
  k < Fintype.card V := by
-- proof
  apply SimpleGraph.IsVertexConnected.card_gt hG

/--
[IsVertexConnected.connected_induce_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma IsVertexConnected_connected_induce_compl_eq
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (hG : G.IsVertexConnected k)
  (hS : S.card < k) :
-- imply
  (G.induce (S : Set V)ᶜ).Connected := by
-- proof
  apply SimpleGraph.IsVertexConnected.connected_induce_compl hG S hS

/--
[IsVertexConnected.connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma IsVertexConnected_connected_eq
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
-- given
  (hG : G.IsVertexConnected k)
  (hk : 0 < k) :
-- imply
  G.Connected := by
-- proof
  apply SimpleGraph.IsVertexConnected.connected hG hk

/--
[IsVertexConnected.connected_compl_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma IsVertexConnected_connected_compl_singleton_eq
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
  {v : V}
-- given
  (hG : G.IsVertexConnected k)
  (hk : 1 < k) :
-- imply
  (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
-- proof
  apply SimpleGraph.IsVertexConnected.connected_compl_singleton hG hk v

/--
[isVertexConnected_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma isVertexConnected_two_iff_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  G.IsVertexConnected 2 ↔
    2 < Fintype.card V ∧ G.Connected ∧
    ∀ v, (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
-- proof
  apply SimpleGraph.isVertexConnected_two_iff

/--
[IsVertexConnected.two_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma IsVertexConnected_two_le_degree_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {v : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  2 ≤ G.degree v := by
-- proof
  apply SimpleGraph.IsVertexConnected.two_le_degree hG v

/--
[IsVertexConnected.exists_cycle_through](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma IsVertexConnected_exists_cycle_through_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  ∃ c : G.Walk x x, c.IsCycle := by
-- proof
  apply SimpleGraph.IsVertexConnected.exists_cycle_through hG x


-- created on 2026-10-20
