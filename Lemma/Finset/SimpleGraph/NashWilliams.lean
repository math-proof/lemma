import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.NashWilliams
open MathlibExt.Combinatorics.SimpleGraph.NashWilliamsWanted


/--
[nash_williams_arboricity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/NashWilliams.lean)
-/
@[path]
private lemma nash_williams_arboricity_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ} :
-- imply
  (∃ C : G.EdgeLabeling (Fin k), IsArboricityColoring C) ↔
    ∀ (U : Finset V), U.Nonempty →
    (G.induce (U : Set V)).edgeFinset.card ≤ k * (U.card - 1) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.NashWilliamsWanted.nash_williams_arboricity G k


-- created on 2026-10-20
