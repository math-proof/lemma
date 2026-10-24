/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
import sympy.atlas.v1.Atlas.TensorCategories.code.ConcreteModuleCategories

set_option autoImplicit false

universe v u

namespace CategoryTheory
namespace InternalHomEssSurjInst

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Equip an object `M` of `C` with the canonical structure of a right module over the
unit monoid `𝟙_ C`, with action given by the right unitor `ρ_M`. -/
def unitRightModObj' (M : C) : RightModObj (𝟙_ C) M where
  act := (ρ_ M).hom
  act_unit := by simp
  act_assoc := by
    simp only [MonObj.mul_def, rightUnitor_naturality]
    simp

/-- The functor sending an object `V` of `C` to itself viewed as a right `𝟙_ C`-module
via `unitRightModObj'`, and a morphism to itself. -/
@[simps]
noncomputable def unitInternalHomFunctor' :
    C ⥤ RightMod_ (A := 𝟙_ C) where
  obj V := ⟨V, unitRightModObj' C V⟩
  map {V W} f := {
    hom := f
    comm := by simp [unitRightModObj']
  }

/-- The `InternalHomData` for `C` acting on itself with generator `𝟙_ C`, endomorphism
algebra `𝟙_ C`, and functor `unitInternalHomFunctor'`. -/
noncomputable instance unitInternalHomData' :
    InternalHomData C C where
  gen := 𝟙_ C
  endAlgebra := ⟨𝟙_ C⟩
  F := unitInternalHomFunctor' C

/-- Every right module over the unit monoid `𝟙_ C` has its action map equal to the right
unitor of the underlying object, i.e. `L.mod.act = (ρ_ L.X).hom`. -/
theorem rightMod_unit_act_eq' (L : RightMod_ (A := 𝟙_ C)) :
    L.mod.act = (ρ_ L.X).hom := by
  have h := L.mod.act_unit
  simp at h
  exact h

/-- For each right `𝟙_ C`-module `L`, the canonical isomorphism between the image of
`L.X` under `unitInternalHomFunctor'` and `L` itself, with identity underlying morphism. -/
noncomputable def rightModUnitIso' (L : RightMod_ (A := 𝟙_ C)) :
    (unitInternalHomFunctor' C).obj L.X ≅ L where
  hom := {
    hom := 𝟙 L.X
    comm := by
      simp [unitInternalHomFunctor', unitRightModObj']
      exact (rightMod_unit_act_eq' C L).symm
  }
  inv := {
    hom := 𝟙 L.X
    comm := by
      simp [unitInternalHomFunctor', unitRightModObj']
      exact rightMod_unit_act_eq' C L
  }

/-- Essential surjectivity of the unit internal Hom functor: every right `𝟙_ C`-module is
isomorphic to one in the image of `unitInternalHomFunctor'`. -/
noncomputable instance unitInternalHomEssSurj' :
    InternalHomEssSurj C C where
  essSurj := Functor.EssSurj.mk (fun L =>
    ⟨L.X, ⟨rightModUnitIso' C L⟩⟩)

end InternalHomEssSurjInst

end CategoryTheory
