/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triHexPlanePeriod : AddMonoidHom (Site 2) Complex where
  toFun z := (z 0 : Real) + (z 1 : Real) * Complex.I
  map_zero' := by simp
  map_add' z w := by
    apply Complex.ext <;> simp

end StatMech.FK.PeriodicPlanar
