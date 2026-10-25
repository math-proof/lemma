import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec3Morphisms
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite VarietyMorphism


namespace VarietyMorphism

/--
[continuous_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Morphisms.lean)
-/
@[path]
lemma continuous_base
  {X Y Z : Scheme.{u}}
  {f : VarietyMorphism X Y} :
-- imply
  Continuous (f : X → Y) :=
-- proof
  f.continuous

end VarietyMorphism

namespace VarietyMorphism

/--
[pullback_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Morphisms.lean)
-/
@[path]
lemma pullback_id
  {X Y Z : Scheme.{u}}
  {U : X.Opens} :
-- imply
  pullbackSections (𝟙 X : VarietyMorphism X X) U = 𝟙 Γ(X, U) :=
-- proof
  Scheme.Hom.id_app U

end VarietyMorphism

namespace VarietyMorphism

/--
[pullback_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3Morphisms.lean)
-/
@[path]
lemma pullback_comp
  {X Y Z : Scheme.{u}}
  {f : VarietyMorphism X Y}
  {g : VarietyMorphism Y Z}
  {U : Z.Opens} :
-- imply
  pullbackSections (f ≫ g) U = pullbackSections g U ≫ pullbackSections f (g ⁻¹ᵁ U) :=
-- proof
  Scheme.Hom.comp_app f g U

end VarietyMorphism


-- created on 2026-10-23
