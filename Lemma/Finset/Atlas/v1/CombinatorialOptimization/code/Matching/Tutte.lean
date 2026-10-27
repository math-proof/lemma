import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Tutte
open SimpleGraph


namespace SimpleGraph

/--
[oddComponentCount_le_ncard_of_isPerfectMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Tutte.lean)
-/
@[path]
lemma oddComponentCount_le_ncard_of_isPerfectMatching
  [Finite V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {X : Set V}
-- given
  (hM : M.IsPerfectMatching) :
-- imply
  G.oddComponentCount X ≤ X.ncard := by
-- proof
  have := SimpleGraph.not_isTutteViolator_of_isPerfectMatching hM X
  unfold IsTutteViolator at this
  unfold oddComponentCount
  omega

end SimpleGraph

namespace SimpleGraph

/--
[isPerfectMatching_of_oddComponentCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Tutte.lean)
-/
@[path]
lemma isPerfectMatching_of_oddComponentCount_le
  [Finite V]
  {G : SimpleGraph V}
-- given
  (h : ∀ X : Set V, G.oddComponentCount X ≤ X.ncard) :
-- imply
  ∃ M : G.Subgraph, M.IsPerfectMatching := by
-- proof
  rw [SimpleGraph.tutte]
  intro X
  unfold IsTutteViolator
  have := h X
  unfold oddComponentCount at this
  omega

end SimpleGraph

namespace SimpleGraph

/--
[tutte_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Tutte.lean)
-/
@[path]
lemma tutte_theorem
  [Finite V]
  {G : SimpleGraph V} :
-- imply
  (∃ M : G.Subgraph, M.IsPerfectMatching) ↔ ∀ X : Set V, G.oddComponentCount X ≤ X.ncard := by
-- proof
  constructor
  · intro ⟨M, hM⟩ X
    exact oddComponentCount_le_ncard_of_isPerfectMatching hM X
  · exact isPerfectMatching_of_oddComponentCount_le

end SimpleGraph


-- created on 2026-10-23
