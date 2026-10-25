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
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalInteriorBlockSide (L p k : Nat) : Nat :=
  p + k * L + p

def cubicalInteriorBlockHeight (L p k : Nat) :
    Fin (cubicalInteriorBlockSide L p k + 1) :=
  ⟨p, by simp [cubicalInteriorBlockSide]⟩

end
end StatMech.FrontierA
