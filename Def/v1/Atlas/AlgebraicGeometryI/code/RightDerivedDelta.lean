/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RightDerivedDelta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechDerivedInstantiate
import Def.v1.Atlas.AlgebraicGeometryI.code.EffaceableUniversal
import Def.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate.Part2
import Structure.v1.Atlas.AlgebraicGeometryI.code.RightDerivedDelta


section PerDegreeEffaceability

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

end PerDegreeEffaceability


noncomputable section

open CategoryTheory CategoryTheory.Limits

open DerivedFunctorsDefs CohomologyConnection

universe v u

namespace RightDerivedDelta

section DeltaFunctorData

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
         {D : Type*} [Category D] [Abelian D]

/-- Comparison data between an effaceable Čech-type δ-functor `F₁` and an
arbitrary δ-functor `F₂`, packaged as a `CechToDerivedData` instance for
the universal property. -/
def nonSelfCechToDerivedData
    (F₁ F₂ : CohomDeltaFunctor C D) (hF₁ : F₁.IsEffaceable) :
    CechToDerivedData (C := C) (D := D) where
  cech := F₁
  derived := F₂
  cech_effaceable := hF₁

end DeltaFunctorData
end RightDerivedDelta
end
