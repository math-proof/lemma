import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SeparatednessDefinition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SeparatednessDefinition


namespace SeparatednessDefinition

/--
[isSeparatedVariety_iff_diagonal_isClosedImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessDefinition.lean)
-/
@[path]
lemma isSeparatedVariety_iff_diagonal_isClosedImmersion
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  {f : X ⟶ SpecK k} :
-- imply
  IsSeparatedVariety k f ↔ IsClosedImmersion (diagonalMorphism k f) :=
-- proof
  isSeparated_iff f

end SeparatednessDefinition

namespace SeparatednessDefinition

/--
[affine_isSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessDefinition.lean)
-/
@[path]
lemma affine_isSeparated
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  [IsAffine X]
  {f : X ⟶ SpecK k} :
-- imply
  IsSeparatedVariety k f :=
-- proof
  inferInstance

end SeparatednessDefinition

namespace SeparatednessDefinition

/--
[affine_diagonal_isClosedImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessDefinition.lean)
-/
@[path]
lemma affine_diagonal_isClosedImmersion
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  [IsAffine X]
  {f : X ⟶ SpecK k} :
-- imply
  IsClosedImmersion (diagonalMorphism k f) :=
-- proof
  (isSeparatedVariety_iff_diagonal_isClosedImmersion k f).mp (affine_isSeparated k f)

end SeparatednessDefinition


-- created on 2026-10-23
