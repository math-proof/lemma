/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OXModuleDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.OXModuleDef
open CategoryTheory

universe u


namespace AlgebraicGeometry

section General

universe v v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

example (U : C) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.obj.obj (Opposite.op U)) :=
  SheafOfModules.evaluation R (Opposite.op U)

example (M : PresheafOfModules.{v} R.obj)
    {U V : C} (i : Opposite.op V ⟶ Opposite.op U)
    (r : R.obj.obj (Opposite.op V)) (m : M.obj (Opposite.op V)) :
    (ConcreteCategory.hom (M.map i)) (r • m) =
      (ConcreteCategory.hom (R.obj.map i)) r • (ConcreteCategory.hom (M.map i)) m :=
  M.map_smul i r m

end General

section Scheme

variable (X : Scheme.{u})

example : Type (u + 1) := X.Modules

noncomputable example : X.Modules := SheafOfModules.unit X.ringCatSheaf

end Scheme
end AlgebraicGeometry
