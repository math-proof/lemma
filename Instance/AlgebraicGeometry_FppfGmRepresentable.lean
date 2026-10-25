-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FppfGmRepresentable.lean: instance decls only.
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Def.AlgebraicGeometry_FppfGmRepresentable

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace FppfRepresentableGroupSchemeSheaf

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w v₁ u₁ u


section Instances

section ConstantZMod

variable (n : ℕ)

local instance : TopologicalSpace (ZMod n) := ⊥

local instance : DiscreteTopology (ZMod n) := ⟨rfl⟩

local instance : IsTopologicalAddGroup (ZMod n) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

end ConstantZMod

end Instances

section Gates

instance : IsCommMonObj (𝟙_ Scheme.{u}) where
  mul_comm := isTerminalTensorUnit.hom_ext _ _

instance gateTrivialSheafSectionsSubsingleton (T : Scheme.{u}) :
    Subsingleton ((gateTrivialGroupSchemeAbelianSheaf.{u}).obj.obj (op T)) :=
  ⟨fun a b => by
    have h : ∀ x y : Additive (T ⟶ 𝟙_ Scheme.{u}), x = y := fun x y =>
      congrArg Additive.ofMul (isTerminalTensorUnit.hom_ext x.toMul y.toMul)
    exact (fppfAbelianSheafSectionsAddEquiv (𝟙_ Scheme.{u}) T).injective (h _ _)⟩

end Gates

end FppfRepresentableGroupSchemeSheaf
end
