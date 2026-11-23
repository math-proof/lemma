/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.AlgebraicGeometryI.code.CohomologyConnection
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyConnection

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

open SheafCohomology CohomologyP1 DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- The identity morphism on a cohomological delta functor. -/
def CohomDeltaFunctor.idMorphism (F : CohomDeltaFunctor C D) : F.Morphism F where
  η n := 𝟙 (F.T n)
  comm_δ n S hS := by simp

end DerivedFunctorsDefs
end
