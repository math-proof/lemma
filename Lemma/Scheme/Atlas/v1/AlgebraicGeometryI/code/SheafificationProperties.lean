import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafificationProperties
open CategoryTheory CategoryTheory.Limits TopCat Proposition15


namespace Proposition15

/--
[sheafification_isLeftAdjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma sheafification_isLeftAdjoint
  {X : TopCat.{u}} :
-- imply
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).IsLeftAdjoint :=
-- proof
  inferInstance

end Proposition15

namespace Proposition15

/--
[sheafification_universal_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma sheafification_universal_factorization
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  [Category.{u} D]
  [HasWeakSheafify J D]
  {P Q : Cᵒᵖ ⥤ D}
  {η : P ⟶ Q}
-- given
  (hQ : Presheaf.IsSheaf J Q) :
-- imply
  toSheafify J P ≫ sheafifyLift J η hQ = η :=
-- proof
  toSheafify_sheafifyLift J η hQ

end Proposition15

namespace Proposition15

/--
[sheafification_universal_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma sheafification_universal_uniqueness
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  [Category.{u} D]
  [HasWeakSheafify J D]
  {P Q : Cᵒᵖ ⥤ D}
  {η : P ⟶ Q}
  {γ : sheafify J P ⟶ Q}
-- given
  (hQ : Presheaf.IsSheaf J Q)
  (h : toSheafify J P ≫ γ = η) :
-- imply
  γ = sheafifyLift J η hQ :=
-- proof
  sheafifyLift_unique J η hQ γ h

end Proposition15

namespace Proposition15

/--
[sheafification_iso_of_isSheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma sheafification_iso_of_isSheaf
  {C : Type u}
  [Category.{u} C]
  {J : GrothendieckTopology C}
  [Category.{u} D]
  [HasWeakSheafify J D]
  {P : Cᵒᵖ ⥤ D}
-- given
  (hP : Presheaf.IsSheaf J P) :
-- imply
  IsIso (toSheafify J P) :=
-- proof
  isIso_toSheafify J hP

end Proposition15

namespace Proposition15

/--
[sheafification_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma sheafification_exact
  {X : TopCat.{u}} :
-- imply
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology := by
-- proof
  set F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  have hfl : PreservesFiniteLimits F := inferInstance
  have hpc : PreservesColimitsOfSize.{0, 0} F :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).leftAdjoint_preservesColimits
  have hfc : PreservesFiniteColimits F := hpc.preservesFiniteColimits
  exact ((F.exact_tfae.out 3 2).mp
    (show PreservesFiniteLimits F ∧ PreservesFiniteColimits F from ⟨hfl, hfc⟩))

end Proposition15

namespace Proposition15

/--
[stalkFunctor_preservesHomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma stalkFunctor_preservesHomology
  {X : TopCat.{u}}
  {x : X} :
-- imply
  (Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesHomology := by
-- proof
  set F := Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hfl : PreservesFiniteLimits F := inferInstance
  have hpc : PreservesColimitsOfSize.{0, 0} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  have hfc : PreservesFiniteColimits F := hpc.preservesFiniteColimits
  exact ((F.exact_tfae.out 3 2).mp
    (show PreservesFiniteLimits F ∧ PreservesFiniteColimits F from ⟨hfl, hfc⟩))

end Proposition15

namespace Proposition15

/--
[exact_iff_stalkwise_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafificationProperties.lean)
-/
@[path]
lemma exact_iff_stalkwise_exact
  {X : TopCat.{u}}
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} :
-- imply
  S.Exact ↔ ∀ x : X, (S.map (Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact :=
-- proof
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

end Proposition15


-- created on 2026-10-23
