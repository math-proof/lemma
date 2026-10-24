/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.CategoryTheory.Yoneda
import sympy.atlas.v1.Atlas.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import sympy.atlas.v1.Atlas.TensorCategories.code.PivotalSpherical
import sympy.atlas.v1.Atlas.TensorCategories.code.CategoricalFreeness

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]


def doubleDual (X : C) : C :=
  HasRightDual.rightDual (HasRightDual.rightDual X)
/-- Data of a distinguished invertible object `L_ρ ∈ C` (Definition 1.51.4): an object
whose tensor product with every projective `P` is naturally isomorphic to `P^{**}`, and
which is fixed by the double-dual functor. -/
class HasDistinguishedInvertibleData where
  distinguished : C
  doubleDual_iso_tensor : ∀ (P : C) [Projective P],
    Nonempty (doubleDual P ≅ distinguished ⊗ P)
  doubleDual_self : Nonempty (doubleDual distinguished ≅ distinguished)


/-- The property that an object `X` has Frobenius-Perron dimension equal to one with
respect to the supplied `FPdimFunction`. -/
def HasFPdimOne {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (f : FPdimFunction (C := C)) (X : C) : Prop := f.fpDim X = 1

/-- Existence of an `FPdimFunction` on `C` witnessing that the distinguished invertible
object has Frobenius-Perron dimension one. -/
structure DistinguishedInvertibleData (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] where
  obj : C
  invertible : IsInvertibleObject obj
  doubleDual_tensor : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ obj ⊗ P)
  doubleDual_self : Nonempty (doubleDual obj ≅ obj)

/-- Package the `HasDistinguishedInvertibleData` instance into the bundled
`DistinguishedInvertibleData` structure. -/
variable (C) in
/-- Data needed to extend a pivotal-style structure from projective objects to all of `C`:
a way to extend a natural isomorphism `P ≅ P^{**}` (for projective `P`) to all objects,
together with the required naturality, monoidality, and unit-trace conditions. -/
class HasDoubleDualExtension where
  extend_pivotalIso :
    (∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) →
    (∀ (X : C), X ≅ (Xᘁ)ᘁ)
  extend_pivotalIso_natural :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P))
      {V W : C} (f : V ⟶ W),
    f ≫ (extend_pivotalIso hProj W).hom =
      (extend_pivotalIso hProj V).hom ≫ (fᘁ)ᘁ
  extend_tensorCoherenceIso :
    (∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) →
    (∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ)
  extend_monoidality :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P))
      (V W : C),
    (extend_pivotalIso hProj (V ⊗ W)).hom =
      ((extend_pivotalIso hProj V).hom ⊗ₘ (extend_pivotalIso hProj W).hom) ≫
        (extend_tensorCoherenceIso hProj V W).hom
  extend_dimUnit :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)),
    TensorCategories.leftQuantumTrace C (extend_pivotalIso hProj (𝟙_ C)).hom = 𝟙 (𝟙_ C)

/-- Construct a `HasDoubleDualExtension` instance from a canonical choice of pivotal-style
data already defined on all objects of `C`. -/
@[reducible] noncomputable def hasDoubleDualExtensionOfCanonical
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (j : ∀ (X : C), X ≅ (Xᘁ)ᘁ)
    (j_nat : ∀ {V W : C} (f : V ⟶ W), f ≫ (j W).hom = (j V).hom ≫ (fᘁ)ᘁ)
    (tc : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ)
    (j_mon : ∀ (V W : C), (j (V ⊗ W)).hom = ((j V).hom ⊗ₘ (j W).hom) ≫ (tc V W).hom)
    (j_dimUnit : TensorCategories.leftQuantumTrace C (j (𝟙_ C)).hom = 𝟙 (𝟙_ C))
    : HasDoubleDualExtension C where
  extend_pivotalIso _ := j
  extend_pivotalIso_natural _ := j_nat
  extend_tensorCoherenceIso _ := tc
  extend_monoidality _ := j_mon
  extend_dimUnit _ := j_dimUnit

/-- Every pivotal category admits a `HasDoubleDualExtension` instance, given by the
ambient pivotal data. -/
noncomputable instance hasDoubleDualExtension_of_pivotal
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [PivotalCategory C] : HasDoubleDualExtension C :=
  hasDoubleDualExtensionOfCanonical
    PivotalCategory.pivotalIso
    PivotalCategory.naturality
    PivotalCategory.tensorCoherenceIso
    PivotalCategory.monoidality
    PivotalCategory.dimUnit


/-- Build a pivotal structure on `C` from a family of double-dual isomorphisms on
projective objects together with a `HasDoubleDualExtension` instance. -/
@[reducible] noncomputable def pivotalFromProjectiveDoubleDual
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDoubleDualExtension C]
    (hDoubleDual : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) :
    PivotalCategory C where
  pivotalIso := HasDoubleDualExtension.extend_pivotalIso hDoubleDual
  tensorCoherenceIso := HasDoubleDualExtension.extend_tensorCoherenceIso hDoubleDual
  naturality := HasDoubleDualExtension.extend_pivotalIso_natural hDoubleDual
  monoidality := HasDoubleDualExtension.extend_monoidality hDoubleDual
  dimUnit := HasDoubleDualExtension.extend_dimUnit hDoubleDual

/-- If an invertible object `D` satisfies `D ⊗ P ≅ 𝟙_C ⊗ P` for every projective `P`
(and the unit is projective), then `D` is isomorphic to the unit. -/
namespace HasDistinguishedInvertible

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [HasDistinguishedInvertibleData C]


open scoped TensorProduct in
/-- A quasi-Hopf algebra over `k`: an algebra `H` equipped with a coproduct, counit, an
invertible associator `Φ`, an antipode together with elements `α, β ∈ H`, and a left
`H`-module structure on the linear dual `H^*`. -/
class IsQuasiHopfAlgebra (k : Type*) (H : Type*) [Field k] [Ring H] [Algebra k H] where
  comul : H →ₐ[k] H ⊗[k] H
  counit : H →ₐ[k] k
  rTensor_counit_comp_comul :
    counit.toLinearMap.rTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k k H) 1
  lTensor_counit_comp_comul :
    counit.toLinearMap.lTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k H k).flip 1
  Φ : H ⊗[k] H ⊗[k] H
  Φ_invertible : ∃ Ψ : H ⊗[k] H ⊗[k] H, Φ * Ψ = 1 ∧ Ψ * Φ = 1
  antipode : H ≃ₗ[k] H
  antipode_anti_mul : ∀ x y : H, antipode (x * y) = antipode y * antipode x
  antipode_one : antipode 1 = 1
  α : H
  β : H
  leftModuleDual : Module H (Module.Dual k H)

/-- The property of being a quasi-Frobenius algebra (placeholder predicate used in the
proof of Corollary 1.51.5). -/
namespace DistinguishedInvertiblePivotalEquiv

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [HasDistinguishedInvertibleData C] [HasDoubleDualExtension C] [Projective (𝟙_ C)]

/-- The distinguished invertible object `D` is isomorphic to the unit if and only if `C`
admits a pivotal structure. -/
end DistinguishedInvertiblePivotalEquiv

end


/-- The monoidal unit `𝟙_C` is always an invertible object, with both inverses given by
the unit isomorphisms. -/
@[reducible]
def unitIsInvertibleObject
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    IsInvertibleObject (𝟙_ C) where
  tensorInverse := 𝟙_ C
  compIso := λ_ (𝟙_ C)
  invCompIso := λ_ (𝟙_ C)

/-- Any pivotal category carries a `HasDistinguishedInvertibleData` instance whose
distinguished invertible object is the monoidal unit. -/
instance hasDistinguishedInvertibleDataOfPivotal
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [piv : PivotalCategory C] :
    HasDistinguishedInvertibleData C where
  distinguished := 𝟙_ C
  doubleDual_iso_tensor := fun P _ =>
    ⟨(piv.pivotalIso P).symm.trans (λ_ P).symm⟩
  doubleDual_self := ⟨(piv.pivotalIso (𝟙_ C)).symm⟩

end CategoryTheory
