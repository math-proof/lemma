module
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part2
open Finset Filter Topology
open scoped BigOperators symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable section

def cubicalInteriorBlockCentralSheet (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYSheet (a := k * L) (b := k * L) (c := 0) (0 : Fin 1)).map
    (cubicalPlaquetteChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))

def cubicalInteriorBlockCentralLoop (L p k : Nat) :
    Finset (CubicalEdge
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  (cubicalXYLoop (a := k * L) (b := k * L) (c := 0) (0 : Fin 1)).map
    (cubicalEdgeChart p p p
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide])
      (by simp [cubicalInteriorBlockSide]))

end
end StatMech.FrontierA
