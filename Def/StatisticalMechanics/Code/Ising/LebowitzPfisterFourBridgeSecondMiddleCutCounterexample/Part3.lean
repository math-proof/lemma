/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part2
open Finset


namespace StatMech.Ising

noncomputable section

def fourBridgeSecondMiddleCutCounterexampleA : Real := 1029 / 1412

def fourBridgeSecondMiddleCutCounterexampleB : Real := 419 / 1412

def fourBridgeSecondMiddleCutCounterexampleC : Real := 955 / 1412

def fourBridgeSecondMiddleCutCounterexampleD : Real := 281 / 1412


end
end StatMech.Ising
