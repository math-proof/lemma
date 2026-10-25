/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsConsolidation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RightDerivedDelta
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.EffaceableUniversal
import Def.v1.Atlas.AlgebraicGeometryI.code.RightDerivedDelta
import Def.v1.Atlas.AlgebraicGeometryI.code.EffaceableUniversal


noncomputable section

open CategoryTheory CategoryTheory.Limits

open DerivedFunctorsDefs CohomologyConnection

universe v u


section PartA

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- For a left-exact additive functor `F : C ⥤ D`, the zeroth right derived functor of `F`
evaluated at `X` is naturally isomorphic to `F.obj X`. -/
def rightDerivedZero_obj_iso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (X : C) : (F.rightDerived 0).obj X ≅ F.obj X :=
  F.rightDerivedZeroIsoSelf.app X

end PartA
end
