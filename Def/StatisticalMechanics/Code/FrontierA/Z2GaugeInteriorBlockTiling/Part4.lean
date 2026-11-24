module
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part3
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

def cubicalInteriorBlockFullSheet (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalXYSheet (cubicalInteriorBlockHeight L p k)

end
end StatMech.FrontierA
