import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace FppfRepresentableGroupSchemeSheaf

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w v₁ u₁ u

section TypeValued

end TypeValued

section StructuredValues

end StructuredValues

section GroupSchemeOverZ

variable (G : Scheme.{u}) [GrpObj G]

end GroupSchemeOverZ

section SectionsIdentification

variable (G : Scheme.{u}) [GrpObj G]

end SectionsIdentification

section GroupSchemeOverBase

variable (S : Scheme.{u})

abbrev fppfTopologyOver : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

end GroupSchemeOverBase

section UnitsDescent

variable {C : Type u₁} [Category.{v₁} C]

end UnitsDescent

section Instances

abbrev affineLineOverZ : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

section ConstantZMod

variable (n : ℕ)

end ConstantZMod

end Instances

section Gates

end Gates

end FppfRepresentableGroupSchemeSheaf
