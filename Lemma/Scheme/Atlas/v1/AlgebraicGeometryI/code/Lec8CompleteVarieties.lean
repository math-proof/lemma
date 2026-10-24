import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec8CompleteVarieties
open AlgebraicGeometry CategoryTheory Limits Formalization Formalization.Lec8CompleteVarieties


namespace Formalization.Lec8CompleteVarieties

/--
[lemma19_ii_image_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8CompleteVarieties.lean)
-/
@[path]
lemma lemma19_ii_image_complete
  {X Z S : Scheme.{u}}
  {f : X ⟶ Z}
  [hXp : IsProper hX]
  [IsSeparated hZ]
-- given
  (hX : X ⟶ S)
  (hZ : Z ⟶ S)
  (hcomm : f ≫ hZ = hX) :
-- imply
  IsClosedImmersion f.imageι ∧ IsProper f.toImage := by
-- proof
  have hfhZ_proper : IsProper (f ≫ hZ) := hcomm ▸ hXp
  have hf_proper : IsProper f := @IsProper.of_comp _ _ _ f hZ hfhZ_proper _
  have hfi : IsProper (f.toImage ≫ f.imageι) := by
    rwa [f.toImage_imageι]
  exact ⟨inferInstance, @IsProper.of_comp _ _ _ f.toImage f.imageι hfi inferInstance⟩

end Formalization.Lec8CompleteVarieties


-- created on 2026-10-23
