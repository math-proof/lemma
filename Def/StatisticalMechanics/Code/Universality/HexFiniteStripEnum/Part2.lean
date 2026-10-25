/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part2


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


noncomputable def hexStrip_finiteRegion (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    HexFiniteRegion where
  verts := hexStrip_verts M
  mids := M
  start := a
  start_mem := ha
  vertexBound := hexStrip_vertexBound M

end StatMech.Universality
