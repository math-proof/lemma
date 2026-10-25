-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FppfCohomologyLES.lean: instance decls only.
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

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES


section FppfSite

open AlgebraicGeometry

instance fppfSheavesIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} Scheme.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall Scheme.fppfTopology Ab.{u + 1}


end FppfSite


end FppfCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

