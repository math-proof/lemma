import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.StrongSquareCycle
open SimpleGraph


namespace SimpleGraph

/--
[hasStrongSquareCycle_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/StrongSquareCycle.lean)
-/
@[path]
lemma hasStrongSquareCycle_iff
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {x : V} :
-- imply
  G.HasStrongSquareCycle x ↔
    ∃ p : G.square.Walk x x, p.IsHamiltonianCycle ∧
    G.Adj x p.snd ∧ G.Adj p.penultimate x :=
-- proof
  Iff.rfl

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
