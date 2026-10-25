/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
open Equiv


namespace StatMech.FrontierD

theorem fkRectClosedMedialPairing_eq_not_vertexParity
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectClosedMedialPairing R v = !fkMedialVertexParity v := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectClosedMedialPairing, fkRectClosedPairingAtEdge,
      fkMedialVertexParity, fkRectMedialVertexOfEdge_fst_val,
      fkRectMedialVertexOfEdge_snd, hy, Bool.toNat]


theorem fkRectConfigurationToMedialPairing_empty (R : FKRectTorus) :
    fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R ∅) = fkRectClosedMedialPairing R := by
  funext v
  simp [fkRectConfigurationToMedialPairing_apply,
    fkRectConfigurationOfEdges, fkRectClosedMedialPairing]


end StatMech.FrontierD
