import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothPointVariety
open AlgebraicGeometry IsLocalRing


/--
[Scheme.isSmoothAtPoint_iff_isRegularLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean)
-/
@[path]
lemma Scheme.isSmoothAtPoint_iff_isRegularLocalRing
  {X : Scheme.{u}}
  [IsLocallyNoetherian X]
  {x : X} :
-- imply
  Scheme.IsSmoothAtPoint X x ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
-- proof
  Iff.rfl

/--
[Scheme.isSmoothAtPoint_iff_spanFinrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean)
-/
@[path]
lemma Scheme.isSmoothAtPoint_iff_spanFinrank
  {X : Scheme.{u}}
  [IsLocallyNoetherian X]
  {x : X}
  [IsLocalRing (X.presheaf.stalk x)]
  [IsNoetherianRing (X.presheaf.stalk x)] :
-- imply
  Scheme.IsSmoothAtPoint X x ↔ (maximalIdeal (X.presheaf.stalk x)).spanFinrank = ringKrullDim (X.presheaf.stalk x) := by
-- proof
  unfold Scheme.IsSmoothAtPoint
  exact isRegularLocalRing_iff (X.presheaf.stalk x)

/--
[Scheme.isSmoothAtPoint_iff_finrank_cotangentSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean)
-/
@[path]
lemma Scheme.isSmoothAtPoint_iff_finrank_cotangentSpace
  {X : Scheme.{u}}
  [IsLocallyNoetherian X]
  {x : X}
  [IsLocalRing (X.presheaf.stalk x)]
  [IsNoetherianRing (X.presheaf.stalk x)] :
-- imply
  Scheme.IsSmoothAtPoint X x ↔ (Module.finrank (ResidueField (X.presheaf.stalk x)) (CotangentSpace (X.presheaf.stalk x)) : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
-- proof
  unfold Scheme.IsSmoothAtPoint
  exact IsRegularLocalRing.iff_finrank_cotangentSpace (R := (X.presheaf.stalk x))


-- created on 2026-10-23
