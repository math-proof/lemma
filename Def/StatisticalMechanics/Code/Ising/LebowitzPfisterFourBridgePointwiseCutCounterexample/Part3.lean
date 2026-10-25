/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample.Part2
open Finset


namespace StatMech.Ising

noncomputable section

def fourBridgePointwiseCutCounterexampleA : Real := 2 / 3

def fourBridgePointwiseCutCounterexampleB : Real := 4 / 3

def fourBridgePointwiseCutCounterexampleC : Real := 2

def fourBridgePointwiseCutCounterexampleD : Real := 1 / 3


end
end StatMech.Ising
