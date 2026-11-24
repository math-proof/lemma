module
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Def.AlgebraicGeometry_FppfGmRepresentable
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000


public section

-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FppfGmRepresentable.lean: instance decls only.

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
