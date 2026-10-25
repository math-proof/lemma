import Mathlib.CategoryTheory.Sites.Continuous
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Instance.AlgebraicGeometry_FppfCohomologyLES

universe v' u' wE vE uE v₁ v₂ u₁ u₂ u w' w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Abelian.Ext

variable {C : Type uE} [Category.{vE} C] [Abelian C] [HasExt.{wE} C]

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme

section SpecInt

end SpecInt

end AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits Opposite AlgebraicGeometry FppfCohomologyLES

namespace EtaleCohomologyLES

section GenericChangeOfTopology

variable {C : Type u} [Category.{v} C]

end GenericChangeOfTopology

section EtaleSite

section WithLocalInstances

variable [HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})]

noncomputable abbrev EtaleH (F : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

end WithLocalInstances

end EtaleSite

section EtaleFppfChangeOfTopology

section WithLocalInstances

variable [HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})]
  [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

end WithLocalInstances

end EtaleFppfChangeOfTopology

section SpecInt

end SpecInt

end EtaleCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

end GenericSite

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

end WithLocalInstances

end FppfSite

end FppfCohomologyLES
