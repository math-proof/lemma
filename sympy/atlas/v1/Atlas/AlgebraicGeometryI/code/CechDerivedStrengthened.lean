/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate
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

/-- Data witnessing a comparison between Čech and derived-functor cohomology as delta functors,
with mutually inverse morphisms in degree zero and effaceability hypotheses to extend the inverse
to all degrees. -/
structure CechDerivedComparisonData where
  cech : CohomDeltaFunctor C D
  derived : CohomDeltaFunctor C D
  cech_effaceable : cech.IsEffaceable
  derived_effaceable : derived.IsEffaceable
  forward : cech.Morphism derived
  backward : derived.Morphism cech
  forward_backward_zero : forward.η 0 ≫ backward.η 0 = 𝟙 (cech.T 0)
  backward_forward_zero : backward.η 0 ≫ forward.η 0 = 𝟙 (derived.T 0)

variable (data : CechDerivedComparisonData (C := C) (D := D))


/-- A `CechDerivedIsomorphism` enriched with explicit degree-zero invertibility witnesses,
suitable for promoting the comparison to all degrees. -/
structure CechDerivedFullComparison extends
    CechDerivedIsomorphism (C := C) (D := D) where
  forward_backward_zero :
    toCechDerivedIsomorphism.forward.η 0 ≫
    toCechDerivedIsomorphism.backward.η 0 =
    𝟙 (toCechDerivedIsomorphism.cech.T 0)
  backward_forward_zero :
    toCechDerivedIsomorphism.backward.η 0 ≫
    toCechDerivedIsomorphism.forward.η 0 =
    𝟙 (toCechDerivedIsomorphism.derived.T 0)

/-- Repackage a `CechDerivedFullComparison` as `CechDerivedComparisonData`. -/
def CechDerivedFullComparison.toComparisonData
    (comp : CechDerivedFullComparison (C := C) (D := D)) :
    CechDerivedComparisonData (C := C) (D := D) where
  cech := comp.cech
  derived := comp.derived
  cech_effaceable := comp.cech_effaceable
  derived_effaceable := comp.derived_effaceable
  forward := comp.forward
  backward := comp.backward
  forward_backward_zero := comp.forward_backward_zero
  backward_forward_zero := comp.backward_forward_zero
