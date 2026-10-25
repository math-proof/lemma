/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Structure.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
set_option maxHeartbeats 800000


noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace DerivedFunctorsDefs

variable (C : Type u) [Category.{v} C] [Abelian C]
         (D : Type*) [Category D] [Abelian D]

variable {C D}

section RightDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- The `n`-th right derived functor of an additive functor `F : C ⥤ D`. -/
def rightDerivedFunctor (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.rightDerived n

/-- The induced natural transformation between `n`-th right derived functors from a natural
transformation `F ⟶ G`. -/
def rightDerivedNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) : rightDerivedFunctor F n ⟶ rightDerivedFunctor G n :=
  NatTrans.rightDerived α n

/-- For a left-exact additive functor, the zeroth right derived functor is naturally
isomorphic to the functor itself. -/
def rightDerivedZeroIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    rightDerivedFunctor F 0 ≅ F :=
  F.rightDerivedZeroIsoSelf

/-- The canonical natural transformation from `F` to its zeroth right derived functor. -/
def toRightDerivedZero (F : C ⥤ D) [F.Additive] :
    F ⟶ rightDerivedFunctor F 0 :=
  F.toRightDerivedZero

end RightDerived
end DerivedFunctorsDefs
end
