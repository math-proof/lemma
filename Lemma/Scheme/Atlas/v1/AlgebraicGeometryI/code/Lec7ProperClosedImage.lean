import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[closedSubset_compactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProperClosedImage.lean)
-/
@[path]
lemma closedSubset_compactSpace
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [CompactSpace X]
  {Z : Set X}
-- given
  (hZ : IsClosed Z) :
-- imply
  CompactSpace Z :=
-- proof
  isCompact_iff_compactSpace.mp hZ.isCompact

/--
[isClosed_image_of_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProperClosedImage.lean)
-/
@[path]
lemma isClosed_image_of_complete
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [CompactSpace X]
  [T2Space Y]
  {f : X → Y}
  {Z : Set X}
-- given
  (hf : Continuous f)
  (hZ : IsClosed Z) :
-- imply
  IsClosed (f '' Z) :=
-- proof
  hf.isProperMap.isClosedMap Z hZ

/--
[isClosed_range_of_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProperClosedImage.lean)
-/
@[path]
lemma isClosed_range_of_complete
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [CompactSpace X]
  [T2Space Y]
  {f : X → Y}
-- given
  (hf : Continuous f) :
-- imply
  IsClosed (Set.range f) := by
-- proof
  rw [← Set.image_univ]
  exact isClosed_image_of_complete hf isClosed_univ

/--
[prod_compactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7ProperClosedImage.lean)
-/
@[path]
lemma prod_compactSpace
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [CompactSpace X]
  [CompactSpace Y] :
-- imply
  CompactSpace (X × Y) :=
-- proof
  inferInstance


-- created on 2026-10-23
