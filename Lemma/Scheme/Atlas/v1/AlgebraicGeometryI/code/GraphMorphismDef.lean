import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.GraphMorphismDef
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace AlgebraicGeometry

/--
[graphMorphism_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean)
-/
@[path]
lemma graphMorphism_snd
  {S X Y : Scheme.{u}}
  {f : X ⟶ Y}
  {sX : X ⟶ S}
  {sY : Y ⟶ S}
-- given
  (w : sX = f ≫ sY) :
-- imply
  graphMorphism f sX sY w ≫ pullback.snd sX sY = f :=
-- proof
  pullback.lift_snd _ _ _

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[graphMorphism_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean)
-/
@[path]
lemma graphMorphism_id
  {S X Y : Scheme.{u}}
  {f : X ⟶ Y}
  {sX : X ⟶ S}
  {sY : Y ⟶ S}
  {sX : X ⟶ S}
-- given
  (w : sX = f ≫ sY) :
-- imply
  graphMorphism (𝟙 X) sX sX (Category.id_comp sX) = pullback.diagonal sX := by
-- proof
  unfold graphMorphism pullback.diagonal
  congr 1

end AlgebraicGeometry

/--
[graphMorphism_fst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean)
-/
@[path]
private lemma graphMorphism_fst_eq
  {S X Y : Scheme.{u}}
  {f : X ⟶ Y}
  {sX : X ⟶ S}
  {sY : Y ⟶ S}
-- given
  (w : sX = f ≫ sY) :
-- imply
  graphMorphism f sX sY w ≫ pullback.fst sX sY = 𝟙 X := by
-- proof
  apply AlgebraicGeometry.graphMorphism_fst f sX sY w


-- created on 2026-10-23
