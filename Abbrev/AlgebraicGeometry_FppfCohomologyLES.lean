import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.PicardGroup
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Instance.AlgebraicGeometry_FppfCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable abbrev constIntSheaf : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))

end GenericSite

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable abbrev FppfH (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

end WithLocalInstances

end FppfSite

section ElementaryComputations

end ElementaryComputations

end FppfCohomologyLES

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
