/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechDerivedInstantiate
import Structure.v1.Atlas.AlgebraicGeometryI.code.CechDerivedStrengthened


noncomputable section

open CategoryTheory CategoryTheory.Limits

open DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

variable (data : CechDerivedComparisonData (C := C) (D := D))


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

end DerivedFunctorsDefs
end
