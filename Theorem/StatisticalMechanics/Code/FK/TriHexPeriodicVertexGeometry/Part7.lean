/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part7
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


@[simp] theorem hexagonalPlaneVertex_apply (u : HexVertex) :
    hexagonalPlaneVertex u = hexagonalPlaneVertexValue u := rfl

@[simp] theorem hexagonalPlaneVertex_shift (z : Site 2) (u : HexVertex) :
    hexagonalPlaneVertex (hexagonal.shift z u) =
      hexagonalPlaneVertex u + triHexPlanePeriod z := by
  rcases u with ⟨x, b⟩
  change triHexPlanePeriod (x + z) + hexagonalFaceCenterOffset b =
    (triHexPlanePeriod x + hexagonalFaceCenterOffset b) +
      triHexPlanePeriod z
  rw [map_add]
  abel


theorem hexagonalPlaneVertex_bounded_finite (R : Real) :
    {u : HexVertex | ‖(hexagonalPlaneVertex u : Complex)‖ <= R}.Finite := by
  let K : Set (Site 2) := {z | ‖triHexPlanePeriod z‖ <= R + 1}
  have hK : K.Finite := triHexPlanePeriod_bounded_finite (R + 1)
  apply (hK.prod Set.finite_univ).subset
  intro u hu
  constructor
  · change ‖triHexPlanePeriod u.1‖ <= R + 1
    have hsplit : triHexPlanePeriod u.1 =
        hexagonalPlaneVertexValue u - hexagonalFaceCenterOffset u.2 := by
      simp [hexagonalPlaneVertexValue]
    rw [hsplit]
    exact (norm_sub_le _ _).trans
      (add_le_add hu (hexagonalFaceCenterOffset_norm_le_one u.2))
  · simp


end StatMech.FK.PeriodicPlanar
