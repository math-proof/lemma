import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.KonigMatchingCover
open MathlibExt.Combinatorics.SimpleGraph.KonigMatchingCoverWanted


/--
[konig_matching_cover_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KonigMatchingCover.lean)
-/
@[path]
private lemma konig_matching_cover_general_eq
  [Finite V]
  {G : SimpleGraph V}
-- given
  (hBip : G.IsBipartite) :
-- imply
  ∃ (M : G.Subgraph) (C : Set V),
    M.IsMatching ∧ G.IsVertexCover C ∧ M.edgeSet.ncard = C.ncard := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.KonigMatchingCoverWanted.konig_matching_cover_general G hBip

/--
[konig_matching_cover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KonigMatchingCover.lean)
-/
@[path]
private lemma konig_matching_cover_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hBip : G.IsBipartite) :
-- imply
  ∃ (M : G.Subgraph) (C : Set V),
    M.IsMatching ∧ G.IsVertexCover C ∧ M.edgeSet.ncard = C.ncard := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.KonigMatchingCoverWanted.konig_matching_cover G hBip


-- created on 2026-10-20
