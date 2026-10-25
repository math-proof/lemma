/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample
open Finset


namespace StatMech.Ising

noncomputable section

theorem fourBridgePointwiseCutCounterexampleWeight_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgePointwiseCutCounterexampleWeight P) = 3 := by
  decide


theorem fourBridgePointwiseCutCounterexampleWeight_logSupermodular :
    ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset,
        fourBridgePointwiseCutCounterexampleWeight P *
            fourBridgePointwiseCutCounterexampleWeight Q <=
          fourBridgePointwiseCutCounterexampleWeight (P ∩ Q) *
            fourBridgePointwiseCutCounterexampleWeight (P ∪ Q) := by
  decide


theorem fourBridgePointwiseCutCounterexampleWeight_complementRatio :
    ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset,
        P ⊆ Q ->
          fourBridgePointwiseCutCounterexampleWeight P *
              fourBridgePointwiseCutCounterexampleWeight
                ((Finset.univ : Finset (Fin 4)) \ Q) <=
            fourBridgePointwiseCutCounterexampleWeight Q *
              fourBridgePointwiseCutCounterexampleWeight
                ((Finset.univ : Finset (Fin 4)) \ P) := by
  decide


end
end StatMech.Ising
