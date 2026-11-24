module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
public import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
public import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
public import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismPureSeamKernel_pos (r : Real) (n : Nat)
    (s q : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismPureSeamKernel r n s q := by
  exact Real.exp_pos _


end
end StatMech.FrontierA
