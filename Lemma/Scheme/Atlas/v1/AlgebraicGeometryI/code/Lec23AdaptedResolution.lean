import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec23AdaptedResolution
open CategoryTheory Category Limits Lec23AdaptedResolution


namespace Lec23AdaptedResolution

/--
[prop43_canonical_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23AdaptedResolution.lean)
-/
@[path]
lemma prop43_canonical_map
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {n : ℕ}
  {M : C}
  {K : Lec23.Resolution M} :
-- imply
  Nonempty ( (HomologicalComplex.homologyFunctor D _ n).obj ((F.mapHomologicalComplex _).obj K.cocomplex) ⟶ (F.rightDerived n).obj M) :=
-- proof
  Lec23.prop43_canonical_map_exists F n K

end Lec23AdaptedResolution

namespace Lec23AdaptedResolution

/--
[prop43_adapted_resolution_computes_derived](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23AdaptedResolution.lean)
-/
@[path]
lemma prop43_adapted_resolution_computes_derived
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {n : ℕ}
  {M : C}
  {K : Lec23.Resolution M}
-- given
  (hadj : ∀ i, Lec23.IsAdjustedToFunctor F (K.cocomplex.X i)) :
-- imply
  Nonempty ( (HomologicalComplex.homologyFunctor D _ n).obj ((F.mapHomologicalComplex _).obj K.cocomplex) ≅ (F.rightDerived n).obj M) :=
-- proof
  Lec23.prop43_iso_when_adjusted F n K hadj

end Lec23AdaptedResolution

namespace Lec23AdaptedResolution

/--
[injective_is_adjusted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23AdaptedResolution.lean)
-/
@[path]
lemma injective_is_adjusted
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {M : C}
  [Injective M] :
-- imply
  Lec23.IsAdjustedToFunctor F M :=
-- proof
  Lec23.injective_isAdjustedToFunctor F M

end Lec23AdaptedResolution


-- created on 2026-10-23
