/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicRadialResidualSummation
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexEndpointRadialShell_lt (n : Nat) :
    forall z, vertexEndpointRadialShell n z < 3 * n + 1 := by
  intro z
  cases z with
  | none => simp [vertexEndpointRadialShell]
  | some x =>
      have hcol := fullVertexColumnIndex_le n x
      have hrow := fullVertexRowIndex_le n x
      simp only [vertexEndpointRadialShell]
      omega


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
