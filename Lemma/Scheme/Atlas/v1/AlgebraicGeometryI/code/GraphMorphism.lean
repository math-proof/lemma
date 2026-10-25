import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.GraphMorphism.Part2
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme


namespace AlgebraicGeometry.Scheme

/--
[graphMor_comp_fst](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean)
-/
@[path]
lemma graphMor_comp_fst
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} :
-- imply
  graphMor f ≫ prod.fst = 𝟙 X := by
-- proof
  simp [graphMor, prod.lift_fst]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/--
[graphMor_comp_snd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean)
-/
@[path]
lemma graphMor_comp_snd
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} :
-- imply
  graphMor f ≫ prod.snd = f := by
-- proof
  simp [graphMor, prod.lift_snd]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/--
[graphMor_of_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean)
-/
@[path]
lemma graphMor_of_id
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} :
-- imply
  graphMor (𝟙 X) = prod.lift (𝟙 X) (𝟙 X) :=
-- proof
  rfl

end AlgebraicGeometry.Scheme

/--
[isPullback_graphMor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean)
-/
@[path]
private lemma isPullback_graphMor_eq
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} :
-- imply
  IsPullback f (graphMor f) (prod.lift (𝟙 Y) (𝟙 Y)) (prod.map f (𝟙 Y)) := by
-- proof
  apply AlgebraicGeometry.Scheme.isPullback_graphMor f


-- created on 2026-10-23
