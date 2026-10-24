import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.AffineVarietyDef
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme

/--
[IsAffineVariety.isAffine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineVarietyDef.lean)
-/
@[path]
lemma IsAffineVariety.isAffine
  {k : Type u}
  [Field k]
  {X : Scheme.{u}}
  [X.Over (Spec (.of k))]
  [h : IsAffineVariety k X] :
-- imply
  IsAffine X :=
-- proof
  ⟨h.toSpecΓ_isIso⟩
attribute [instance] IsAffineVariety.toSpecΓ_isIso IsAffineVariety.locallyOfFiniteType
  IsAffineVariety.isReduced

end AlgebraicGeometry.Scheme


-- created on 2026-10-23
