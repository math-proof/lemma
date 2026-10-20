import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.StrongSquareCycle
open SimpleGraph


/--
[hasStrongSquareCycle_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StrongSquareCycle.lean)
-/
@[path]
private lemma hasStrongSquareCycle_iff_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {x : V} :
-- imply
  G.HasStrongSquareCycle x ↔
    ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
    G.Adj x p.snd ∧ G.Adj p.penultimate x := by
-- proof
  apply SimpleGraph.hasStrongSquareCycle_iff G x


-- created on 2026-10-20
