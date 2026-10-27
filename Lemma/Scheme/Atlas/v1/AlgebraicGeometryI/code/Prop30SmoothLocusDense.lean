import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop30SmoothLocusDense
open AlgebraicGeometry IsLocalRing


/--
[Scheme.mem_smoothLocus'_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop30SmoothLocusDense.lean)
-/
@[path]
lemma Scheme.mem_smoothLocus'_iff
  {X : Scheme.{u}}
  [IsLocallyNoetherian X]
  {x : X} :
-- imply
  x ∈ Scheme.smoothLocus' X ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
-- proof
  Iff.rfl
/-- The smooth locus of a reduced irreducible scheme is open. -/


-- created on 2026-10-23
