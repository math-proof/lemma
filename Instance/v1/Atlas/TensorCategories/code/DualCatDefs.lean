/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCatDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Logic.UnivLE
import Def.v1.Atlas.TensorCategories.code.DualCatDefs
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory ModFun

/-- Hom-sets of module endofunctors of `M` are essentially `v₂`-small whenever `M` is
essentially `v₂`-small, giving a `Small` instance suitable for shrinking morphisms. -/
noncomputable instance DualCatObj'.natTransSmall
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (F G : DualCatObj' C M) : Small.{v₂} (F.toFunctor ⟶ G.toFunctor) :=
  small_of_injective (f := fun η => η.app) (fun _ _ h => NatTrans.ext h)

end CategoryTheory
