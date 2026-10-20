import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Vizing
open MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted


/--
[vizing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Vizing.lean)
-/
@[path]
private lemma vizing_eq
  :
-- imply
  ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    ∃ C : G.EdgeLabeling (Fin (G.maxDegree + 1)), IsProperEdgeColoring C := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted.vizing


-- created on 2026-10-20
