/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample
open Finset


namespace StatMech.Ising

noncomputable section

def fourBridgePointwiseCutCounterexampleMass
    (P : Finset (Fin 4)) : Real :=
  fourBridgePointwiseCutCounterexampleWeight P / 3

end
end StatMech.Ising
