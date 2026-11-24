module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

def fourBridgeSecondMiddleCutCounterexampleMass
    (P : Finset (Fin 4)) : Real :=
  fourBridgeSecondMiddleCutCounterexampleWeight P / 2824

end
end StatMech.Ising
