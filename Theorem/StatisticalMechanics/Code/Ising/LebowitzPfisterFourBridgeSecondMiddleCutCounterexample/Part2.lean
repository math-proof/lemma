/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part2
open Finset


namespace StatMech.Ising

noncomputable section

theorem fourBridgeSecondMiddleCutCounterexampleMass_nonneg
    (P : Finset (Fin 4)) :
    0 <= fourBridgeSecondMiddleCutCounterexampleMass P := by
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  positivity

theorem fourBridgeSecondMiddleCutCounterexampleMass_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgeSecondMiddleCutCounterexampleMass P) = 1 := by
  have hReal :
      (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (fourBridgeSecondMiddleCutCounterexampleWeight P : Real)) = 2824 := by
    exact_mod_cast fourBridgeSecondMiddleCutCounterexampleWeight_sum
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  rw [← Finset.sum_div, hReal]
  norm_num


theorem fourBridgeSecondMiddleCutCounterexampleMass_logSupermodular
    {P Q : Finset (Fin 4)}
    (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset) :
    fourBridgeSecondMiddleCutCounterexampleMass P *
        fourBridgeSecondMiddleCutCounterexampleMass Q <=
      fourBridgeSecondMiddleCutCounterexampleMass (P ∩ Q) *
        fourBridgeSecondMiddleCutCounterexampleMass (P ∪ Q) := by
  have hNat := fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular
    P hP Q hQ
  have hReal :
      (fourBridgeSecondMiddleCutCounterexampleWeight P : Real) *
          fourBridgeSecondMiddleCutCounterexampleWeight Q <=
        (fourBridgeSecondMiddleCutCounterexampleWeight (P ∩ Q) : Real) *
          fourBridgeSecondMiddleCutCounterexampleWeight (P ∪ Q) := by
    exact_mod_cast hNat
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  nlinarith


theorem fourBridgeSecondMiddleCutCounterexample_rankWeights :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 0 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 16 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 1 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 547 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 2 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 1165 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 3 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 584 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 4 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 512 := by
  decide


end
end StatMech.Ising
