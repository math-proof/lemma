import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.BlowupDefinition
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BlowupDefinition
open AlgebraicGeometry


namespace Blowup

/--
[blowup_iso_outside_center](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupProperties.lean)
-/
@[path]
lemma blowup_iso_outside_center
  [CommRing R]
  {I : Ideal R} :
-- imply
  ∃ (U : (blowupAlong I).Opens), ∃ (f : U.toScheme ⟶ AlgebraicGeometry.Spec (.of R)), AlgebraicGeometry.IsOpenImmersion f :=
-- proof
  blowup_iso_away_from_center I

end Blowup

namespace Blowup

/--
[exceptionalLocus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupProperties.lean)
-/
@[path]
lemma exceptionalLocus_isClosed
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  IsClosed ((exceptionalLocusSet π C : Set X.toTopCat)) :=
-- proof
  (exceptionalLocusSet π C).isClosed'

end Blowup

namespace Blowup

/--
[properTransform_eq_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupProperties.lean)
-/
@[path]
lemma properTransform_eq_closure
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {Z C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  (properTransformSet π Z C : Set X.toTopCat) = closure (π.base ⁻¹' ((Z : Set Y.toTopCat) \ (C : Set Y.toTopCat))) :=
-- proof
  rfl

end Blowup

namespace Blowup

/--
[properTransform_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupProperties.lean)
-/
@[path]
lemma properTransform_isClosed
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {Z C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  IsClosed (properTransformSet π Z C : Set X.toTopCat) :=
-- proof
  (properTransformSet π Z C).isClosed'

end Blowup

namespace Blowup

/--
[exceptionalLocus_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupProperties.lean)
-/
@[path]
lemma exceptionalLocus_eq_preimage
  [CommRing R]
  {I : Ideal R}
  {X Y : Scheme}
  {π : X ⟶ Y}
  {C : TopologicalSpace.Closeds Y.toTopCat} :
-- imply
  (exceptionalLocusSet π C : Set X.toTopCat) = π.base ⁻¹' (C : Set Y.toTopCat) :=
-- proof
  rfl

end Blowup


-- created on 2026-10-23
