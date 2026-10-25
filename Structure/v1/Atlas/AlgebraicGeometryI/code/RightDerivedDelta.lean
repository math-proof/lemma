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

/-- Data exhibiting a cohomological δ-functor as the right derived δ-functor
of an additive functor `F : C ⥤ D`: the underlying δ-functor `δF`, an
identification `(δF)^n = F.rightDerived n` in each degree, and effaceability. -/
structure RightDerivedDeltaFunctorData (F : C ⥤ D) [F.Additive] where
  deltaFunctor : CohomDeltaFunctor C D
  degree_eq : ∀ n, deltaFunctor.T n = F.rightDerived n
  effaceable : deltaFunctor.IsEffaceable

end DeltaFunctorData
end RightDerivedDelta
end
