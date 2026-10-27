import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.SmoothVectors
open ContinuousRep
open scoped Manifold


namespace ContinuousRep

/--
[smoothVector_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SmoothVectorsProps.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {I : ModelWithCorners ℝ E H} [LieGroup I ⊤ G]
  {π : ContinuousRep G F} :
-- imply
  π.IsSmoothVector I 0 :=
-- proof
  (π.smoothSubspace I).zero_mem


end ContinuousRep


-- created on 2026-10-23
-- updated on 2026-10-26
