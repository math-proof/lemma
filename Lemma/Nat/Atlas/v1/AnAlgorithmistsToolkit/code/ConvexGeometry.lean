import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.ConvexGeometry.Part2
open Set ConvexGeometry
open scoped Pointwise
open MeasureTheory


namespace ConvexGeometry

/--
[IsConvexBody.convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/ConvexGeometry.lean)
-/
@[path]
lemma IsConvexBody.convex
  [TopologicalSpace E]
  [AddCommGroup E]
  [Module ℝ E]
  {C : Set E}
-- given
  (h : IsConvexBody C) :
-- imply
  Convex ℝ C :=
-- proof
  h.1

end ConvexGeometry

namespace ConvexGeometry

/--
[IsConvexBody.isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/ConvexGeometry.lean)
-/
@[path]
lemma IsConvexBody.isCompact
  [TopologicalSpace E]
  [AddCommGroup E]
  [Module ℝ E]
  {C : Set E}
-- given
  (h : IsConvexBody C) :
-- imply
  IsCompact C :=
-- proof
  h.2.1

end ConvexGeometry

namespace ConvexGeometry

/--
[IsConvexBody.interior_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/ConvexGeometry.lean)
-/
@[path]
lemma IsConvexBody.interior_nonempty
  [TopologicalSpace E]
  [AddCommGroup E]
  [Module ℝ E]
  {C : Set E}
-- given
  (h : IsConvexBody C) :
-- imply
  (interior C).Nonempty :=
-- proof
  h.2.2

end ConvexGeometry

namespace ConvexGeometry

/--
[separating_hyperplane](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/ConvexGeometry.lean)
-/
@[path]
lemma separating_hyperplane
  [TopologicalSpace E]
  [AddCommGroup E]
  [Module ℝ E]
  [T2Space E]
  [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]
  {K : Set E}
  {p : E}
-- given
  (hK : IsConvexBody K)
  (hp : p ∉ K) :
-- imply
  ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ K, f a < u) ∧ u < f p := by
-- proof
  have hclosed : IsClosed K := hK.isCompact.isClosed
  have hconvex : Convex ℝ K := hK.convex
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point hconvex hclosed hp
  exact ⟨f, u, hlt, hgt⟩

end ConvexGeometry


-- created on 2026-10-23
