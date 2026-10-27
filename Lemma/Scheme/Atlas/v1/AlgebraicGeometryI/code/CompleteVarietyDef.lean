import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CompleteVarietyDef
open CategoryTheory AlgebraicGeometry


namespace AlgebraicGeometry

/--
[isComplete_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CompleteVarietyDef.lean)
-/
@[path]
lemma isComplete_iff
  {X S : Scheme.{u}}
  [X.Over S] :
-- imply
  IsComplete X S ↔ IsSeparated (X ↘ S) ∧ UniversallyClosed (X ↘ S) ∧ LocallyOfFiniteType (X ↘ S) := by
-- proof
  simp only [IsComplete, isProper_iff]

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsComplete.mk'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CompleteVarietyDef.lean)
-/
@[path]
lemma IsComplete.mk'
  {X S : Scheme.{u}}
  [X.Over S]
  [IsSeparated (X ↘ S)]
  [UniversallyClosed (X ↘ S)]
  [LocallyOfFiniteType (X ↘ S)] :
-- imply
  IsComplete X S :=
-- proof
  ⟨⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsComplete.isSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CompleteVarietyDef.lean)
-/
@[path]
lemma IsComplete.isSeparated
  {X S : Scheme.{u}}
  [X.Over S]
-- given
  (h : IsComplete X S) :
-- imply
  IsSeparated (X ↘ S) :=
-- proof
  h.toIsSeparated

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsComplete.universallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CompleteVarietyDef.lean)
-/
@[path]
lemma IsComplete.universallyClosed
  {X S : Scheme.{u}}
  [X.Over S]
-- given
  (h : IsComplete X S) :
-- imply
  UniversallyClosed (X ↘ S) :=
-- proof
  h.toUniversallyClosed

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[IsComplete.locallyOfFiniteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CompleteVarietyDef.lean)
-/
@[path]
lemma IsComplete.locallyOfFiniteType
  {X S : Scheme.{u}}
  [X.Over S]
-- given
  (h : IsComplete X S) :
-- imply
  LocallyOfFiniteType (X ↘ S) :=
-- proof
  h.toLocallyOfFiniteType

end AlgebraicGeometry


-- created on 2026-10-23
