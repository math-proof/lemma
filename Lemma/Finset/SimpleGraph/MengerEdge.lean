import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.MengerEdge
open MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted


/--
[menger_edge_max_min](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MengerEdge.lean)
-/
@[path]
private lemma menger_edge_max_min_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {s t : V}
-- given
  (hst : s ≠ t) :
-- imply
  ∃ k : ℕ, ∃ (paths : Fin k → G.Path s t) (C : Finset (Sym2 V)),
    IsEdgeDisjointSTPaths paths ∧
    IsSTEdgeCut G s t C ∧
    C.card = k ∧
    (∀ {l : ℕ} (paths' : Fin l → G.Path s t), IsEdgeDisjointSTPaths paths' → l ≤ k) ∧
    (∀ C' : Finset (Sym2 V), IsSTEdgeCut G s t C' → k ≤ C'.card) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted.menger_edge_max_min s t hst


-- created on 2026-10-20
