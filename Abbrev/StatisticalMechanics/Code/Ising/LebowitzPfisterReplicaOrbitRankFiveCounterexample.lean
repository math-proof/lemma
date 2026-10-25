/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
open scoped symmDiff
open Finset


namespace StatMech.Ising

abbrev LPRankFiveCounterVertex := Fin 8

abbrev LPRankFiveCounterSlot := Fin 5

abbrev LPRankFiveCounterOrientation := Fin 16

abbrev LPRankFiveCounterColoring := Fin 1024

end StatMech.Ising
