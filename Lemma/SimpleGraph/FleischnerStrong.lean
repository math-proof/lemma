import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.FleischnerStrong
open scoped BigOperators
open SimpleGraph


/--
[IsVertexConnected.hasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma IsVertexConnected_hasStrongSquareCycle_eq
  {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  G.HasStrongSquareCycle x := by
-- proof
  apply SimpleGraph.IsVertexConnected.hasStrongSquareCycle hG x


-- created on 2026-10-20
