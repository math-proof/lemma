/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample.Part2
open Finset


namespace StatMech.Ising

noncomputable section

theorem fourBridgePointwiseCutCounterexampleMass_nonneg
    (P : Finset (Fin 4)) :
    0 <= fourBridgePointwiseCutCounterexampleMass P := by
  unfold fourBridgePointwiseCutCounterexampleMass
  positivity

theorem fourBridgePointwiseCutCounterexampleMass_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgePointwiseCutCounterexampleMass P) = 1 := by
  have hReal :
      (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (fourBridgePointwiseCutCounterexampleWeight P : Real)) = 3 := by
    exact_mod_cast fourBridgePointwiseCutCounterexampleWeight_sum
  unfold fourBridgePointwiseCutCounterexampleMass
  rw [← Finset.sum_div, hReal]
  norm_num


theorem fourBridgePointwiseCutCounterexampleMass_logSupermodular
    {P Q : Finset (Fin 4)}
    (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset) :
    fourBridgePointwiseCutCounterexampleMass P *
        fourBridgePointwiseCutCounterexampleMass Q <=
      fourBridgePointwiseCutCounterexampleMass (P ∩ Q) *
        fourBridgePointwiseCutCounterexampleMass (P ∪ Q) := by
  have hNat := fourBridgePointwiseCutCounterexampleWeight_logSupermodular
    P hP Q hQ
  have hReal :
      (fourBridgePointwiseCutCounterexampleWeight P : Real) *
          fourBridgePointwiseCutCounterexampleWeight Q <=
        (fourBridgePointwiseCutCounterexampleWeight (P ∩ Q) : Real) *
          fourBridgePointwiseCutCounterexampleWeight (P ∪ Q) := by
    exact_mod_cast hNat
  unfold fourBridgePointwiseCutCounterexampleMass
  nlinarith


theorem fourBridgePointwiseCutCounterexampleMass_complementRatio
    {P Q : Finset (Fin 4)}
    (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hPQ : P ⊆ Q) :
    fourBridgePointwiseCutCounterexampleMass P *
        fourBridgePointwiseCutCounterexampleMass
          ((Finset.univ : Finset (Fin 4)) \ Q) <=
      fourBridgePointwiseCutCounterexampleMass Q *
        fourBridgePointwiseCutCounterexampleMass
          ((Finset.univ : Finset (Fin 4)) \ P) := by
  have hNat := fourBridgePointwiseCutCounterexampleWeight_complementRatio
    P hP Q hQ hPQ
  have hReal :
      (fourBridgePointwiseCutCounterexampleWeight P : Real) *
          fourBridgePointwiseCutCounterexampleWeight
            ((Finset.univ : Finset (Fin 4)) \ Q) <=
        (fourBridgePointwiseCutCounterexampleWeight Q : Real) *
          fourBridgePointwiseCutCounterexampleWeight
            ((Finset.univ : Finset (Fin 4)) \ P) := by
    exact_mod_cast hNat
  unfold fourBridgePointwiseCutCounterexampleMass
  nlinarith


theorem fourBridgePointwiseCutCounterexample_rankWeights :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 0 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 0 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 1 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 2 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 3 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 0 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 4 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 := by
  decide

end
end StatMech.Ising
