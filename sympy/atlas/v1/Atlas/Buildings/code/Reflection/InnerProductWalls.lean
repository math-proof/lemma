/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Reflection.WallSeparation
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.ReflectionGroupsCoxeter
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Defs
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.FiniteReflectionGroups.Theorems
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.GenericFunctional

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace HyperplaneArrangement

variable {arr : HyperplaneArrangement E}

def ChamberInPositiveHalfSpace (C : arr.Chamber) (η : AffineHyperplane E) : Prop :=
  C.set ⊆ η.positiveHalfSpace

def ChamberInNegativeHalfSpace (C : arr.Chamber) (η : AffineHyperplane E) : Prop :=
  C.set ⊆ η.negativeHalfSpace

def inwardUnitNormal (C : arr.Chamber) (η : AffineHyperplane E)
    [Decidable (ChamberInPositiveHalfSpace C η)] : E :=
  if ChamberInPositiveHalfSpace C η
  then (‖η.normal‖⁻¹) • η.normal
  else (‖η.normal‖⁻¹) • (-η.normal)

end HyperplaneArrangement
