import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Riha
open SimpleGraph


/--
[Walk.isBoundVertex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Riha.lean)
-/
@[path]
private lemma Walk_isBoundVertex_iff_eq
  {G : SimpleGraph V}
  {x : V}
  {c : G.Walk x x}
  {y : V} :
-- imply
  c.IsBoundVertex y ↔ y ∈ c.support ∧ ∀ ⦃z⦄, G.Adj y z → z ∈ c.support := by
-- proof
  apply SimpleGraph.Walk.isBoundVertex_iff c y

/--
[IsVertexConnected.exists_cycle_bound_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Riha.lean)
-/
@[path]
private lemma IsVertexConnected_exists_cycle_bound_vertex_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  ∃ c : G.Walk x x, c.IsCycle ∧ ∃ y, y ≠ x ∧ c.IsBoundVertex y := by
-- proof
  apply SimpleGraph.IsVertexConnected.exists_cycle_bound_vertex hG x


-- created on 2026-10-20
