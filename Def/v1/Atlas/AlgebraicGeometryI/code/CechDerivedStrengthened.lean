/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechDerivedInstantiate


noncomputable section

open CategoryTheory CategoryTheory.Limits

open DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- Composition of morphisms of cohomological delta functors. -/
def CohomDeltaFunctor.compMorphism {F G H : CohomDeltaFunctor C D}
    (m₁ : F.Morphism G) (m₂ : G.Morphism H) : F.Morphism H where
  η n := m₁.η n ≫ m₂.η n
  comm_δ n S hS := by
    simp only [NatTrans.comp_app]


    rw [Category.assoc, m₂.comm_δ n S hS, ← Category.assoc,
        ← Category.assoc, m₁.comm_δ n S hS, Category.assoc]

end DerivedFunctorsDefs
end
