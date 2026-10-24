/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCatDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Logic.UnivLE

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory ModFun

/-- Underlying type of objects of the dual category `C*_M`: module endofunctors of `M`. -/
def DualCatObj'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] :=
  ModuleFunctor' C M M

/-- The property that the module category `M` over `C` is exact: tensoring any object of
`M` with a projective object of `C` yields a projective object. -/
def IsExactModuleCategory'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] : Prop :=
  ∀ (P : C) (N : M), Projective P → Projective (P ⊗ᵐ N)

/-- Hom-sets of module endofunctors of `M` are essentially `v₂`-small whenever `M` is
essentially `v₂`-small, giving a `Small` instance suitable for shrinking morphisms. -/
noncomputable instance DualCatObj'.natTransSmall
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (F G : DualCatObj' C M) : Small.{v₂} (F.toFunctor ⟶ G.toFunctor) :=
  small_of_injective (f := fun η => η.app) (fun _ _ h => NatTrans.ext h)

/-- Category structure on `DualCatObj' C M` whose morphisms are obtained by shrinking
the natural transformations between the underlying module functors. -/
@[reducible]
class HasModuleInternalHom'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] where
  moduleIHom' : M → M → C
  moduleIHomEquiv' : ∀ (X : C) (m n : M),
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom' m n)
  moduleIHomEquiv'_natural : ∀ {X Y : C} (f : X ⟶ Y) (m n : M) (g : Y ⊗ᵐ m ⟶ n),
    moduleIHomEquiv' X m n (f ▷ᵐ m ≫ g) = f ≫ moduleIHomEquiv' Y m n g

export HasModuleInternalHom' (moduleIHom' moduleIHomEquiv' moduleIHomEquiv'_natural)

/-- An exact module category over a rigid tensor category with enough projectives admits
internal `Hom` objects valued in `C`. -/
end CategoryTheory
