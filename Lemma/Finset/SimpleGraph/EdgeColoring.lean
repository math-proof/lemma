import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.EdgeColoring
open MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted


/--
[konig_line_coloring](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeColoring.lean)
-/
@[path]
private lemma konig_line_coloring_eq
  :
-- imply
  ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.IsBipartite → ∃ C : G.EdgeLabeling (Fin G.maxDegree), IsProperEdgeColoring C := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted.konig_line_coloring


-- created on 2026-10-20
