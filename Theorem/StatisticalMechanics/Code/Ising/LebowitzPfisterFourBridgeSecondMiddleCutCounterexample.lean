/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample
open Finset


namespace StatMech.Ising

noncomputable section

theorem fourBridgeSecondMiddleCutCounterexampleWeight_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgeSecondMiddleCutCounterexampleWeight P) = 2824 := by
  decide


theorem fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular :
    ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset,
        fourBridgeSecondMiddleCutCounterexampleWeight P *
            fourBridgeSecondMiddleCutCounterexampleWeight Q <=
          fourBridgeSecondMiddleCutCounterexampleWeight (P ∩ Q) *
            fourBridgeSecondMiddleCutCounterexampleWeight (P ∪ Q) := by
  decide


end
end StatMech.Ising
