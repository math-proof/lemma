/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory/Theorem2116.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory.Theorem2112
import sympy.atlas.v1.Atlas.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Mathlib.CategoryTheory.Monoidal.Mod_

open CategoryTheory MonoidalCategory LeftModCat

namespace CategoryTheory

universe u₁ v₁ u₂ v₂

/-- Predicate asserting that a left `C`-module category `M` is finite (placeholder class used
in the statement of Theorem 2.11.6). -/
class IsFiniteModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  finite : True

/-- Predicate asserting that a left `C`-module category `M` is exact (placeholder class used
in the statement of Theorem 2.11.6(ii)). -/
class IsExactModuleCat
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  exact : True

/-- Predicate asserting that the orbit of `gen` under the `C`-action generates the
Grothendieck group of `M`, used as the generation hypothesis in Theorem 2.11.6(ii). -/
end CategoryTheory
