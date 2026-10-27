import Mathlib
import Initialize.Tactic.Attr.Basic
open AlgebraicGeometry CategoryTheory Topology


/--
[isClosedImmersion_iff_closedRange_embedding_surjectiveOnStalks](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ClosedImmersion.lean)
-/
@[path]
lemma isClosedImmersion_iff_closedRange_embedding_surjectiveOnStalks
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} :
-- imply
  IsClosedImmersion f ↔ IsClosed (Set.range f) ∧ IsEmbedding (f : X → Y) ∧ ∀ x : X, Function.Surjective (ConcreteCategory.hom (f.stalkMap x)) := by
-- proof
  rw [isClosedImmersion_iff, surjectiveOnStalks_iff]
  constructor
  · rintro ⟨hsurj, hclosed⟩
    exact ⟨hclosed.isClosed_range, hclosed.isEmbedding, hsurj⟩
  · rintro ⟨hclosed, hemb, hsurj⟩
    exact ⟨hsurj, IsClosedEmbedding.mk hemb hclosed⟩

/--
[IsClosedImmersion.isClosed_range'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ClosedImmersion.lean)
-/
@[path]
lemma IsClosedImmersion.isClosed_range'
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsClosedImmersion f] :
-- imply
  IsClosed (Set.range f) :=
-- proof
  f.isClosedEmbedding.isClosed_range

/--
[IsClosedImmersion.isEmbedding'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ClosedImmersion.lean)
-/
@[path]
lemma IsClosedImmersion.isEmbedding'
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsClosedImmersion f] :
-- imply
  IsEmbedding (f : X → Y) :=
-- proof
  f.isClosedEmbedding.isEmbedding

/--
[IsClosedImmersion.stalkMap_surjective'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ClosedImmersion.lean)
-/
@[path]
lemma IsClosedImmersion.stalkMap_surjective'
  {X Y : Scheme.{u}}
  {f : X ⟶ Y}
  [IsClosedImmersion f]
  {x : X} :
-- imply
  Function.Surjective (ConcreteCategory.hom (f.stalkMap x)) :=
-- proof
  (surjectiveOnStalks_iff f).mp inferInstance x


-- created on 2026-10-23
