/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Structure.StatisticalMechanics.Code.Universality.HexFiniteRegion


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


namespace HexFiniteRegion

variable (R : HexFiniteRegion)


def inRegion (z : ℂ) : Prop := z ∈ R.mids


end HexFiniteRegion
end StatMech.Universality
