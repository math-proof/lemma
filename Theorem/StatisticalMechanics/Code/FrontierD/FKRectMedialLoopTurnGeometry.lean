module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedEdgeCenterClass
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem fkRectClosedPairing_eq_not_vertexParity
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v) =
      !fkMedialVertexParity v := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = (fkRectTorusMedialEdgeEquiv R).symm e := by
    simp [e]
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectClosedPairingAtEdge, fkMedialVertexParity, hy,
      Bool.toNat]

end
end StatMech.FrontierD
