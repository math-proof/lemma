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
import Def.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsConsolidation


noncomputable section

open CategoryTheory CategoryTheory.Limits

open DerivedFunctorsDefs CohomologyConnection

universe v u


section PartB

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- Placeholder statement that the right derived functors of `F` are independent of the
chosen injective resolution. -/
structure ResolutionIndependence (F : C ⥤ D) [F.Additive] : Prop where
  obj_determined : ∀ (n : ℕ) (X : C),
    ∃! (_ : (F.rightDerived n).obj X = (F.rightDerived n).obj X), True

end PartB
end
