import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.PetersenMatching
open MathlibExt.Combinatorics.SimpleGraph.PetersenMatchingWanted


/--
[petersen_bridgeless_cubic_has_perfect_matching_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/PetersenMatching.lean)
-/
@[path]
private lemma petersen_bridgeless_cubic_has_perfect_matching_general_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hreg : G.IsRegularOfDegree 3)
  (hbridge : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
-- imply
  ∃ M : G.Subgraph, M.IsPerfectMatching := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.PetersenMatchingWanted.petersen_bridgeless_cubic_has_perfect_matching_general G hreg hbridge

/--
[petersen_bridgeless_cubic_has_perfect_matching](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/PetersenMatching.lean)
-/
@[path]
private lemma petersen_bridgeless_cubic_has_perfect_matching_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hreg : G.IsRegularOfDegree 3)
  (hbridge : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
-- imply
  ∃ M : G.Subgraph, M.IsPerfectMatching := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.PetersenMatchingWanted.petersen_bridgeless_cubic_has_perfect_matching G hreg hbridge


-- created on 2026-10-20
