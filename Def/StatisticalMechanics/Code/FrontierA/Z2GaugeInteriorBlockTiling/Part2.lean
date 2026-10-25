/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalInteriorBlockTileSheet
    (L p k : Nat) (q : Fin k × Fin k) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYSheet (a := L) (b := L) (c := 0) (0 : Fin 1)).map
    (cubicalPlaquetteChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))

def cubicalInteriorBlockTileLoop
    (L p k : Nat) (q : Fin k × Fin k) :
    Finset (CubicalEdge
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYLoop (a := L) (b := L) (c := 0) (0 : Fin 1)).map
    (cubicalEdgeChart (p + q.1.val * L) (p + q.2.val * L) p
      (cubicalInteriorBlockTile_fit L p k q.1)
      (cubicalInteriorBlockTile_fit L p k q.2)
      (by simp [cubicalInteriorBlockSide]))

end
end StatMech.FrontierA
