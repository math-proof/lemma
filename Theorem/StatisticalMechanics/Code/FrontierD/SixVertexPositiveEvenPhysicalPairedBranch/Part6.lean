/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part5
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    (hbase : forall n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
      Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          (sixVertexPositiveEvenTorus N 0 hNpos hNeven)
          ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN))
    (hsteps : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations
      N hNpos hNeven) :
    SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven := by
  intro M
  induction M with
  | zero =>
      intro n hn0 hnN
      exact hbase n hn0 hnN
  | succ M ih =>
      intro n hn0 hnN
      obtain ⟨embeddings⟩ := ih n hn0 hnN
      obtain ⟨factorization⟩ := hsteps M n hn0 hnN
      refine ⟨?_⟩
      simpa [Nat.succ_eq_add_one] using factorization.lift embeddings


theorem sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    (hbase : forall n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
      Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          (sixVertexPositiveEvenTorus N 0 hNpos hNeven)
          ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN))
    (hroutes :
      SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings
        N hNpos hNeven) :
    SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven := by
  intro M
  induction M with
  | zero =>
      intro n hn0 hnN
      exact hbase n hn0 hnN
  | succ M ih =>
      intro n hn0 hnN
      obtain ⟨embeddings⟩ := ih n hn0 hnN
      obtain ⟨extension⟩ := hroutes M n hn0 hnN embeddings
      refine ⟨?_⟩
      simpa [Nat.succ_eq_add_one] using extension.lift


theorem sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightSteps
    (hsteps : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations
      4 (by norm_num) (by norm_num)) :
    SixVertexPositiveEvenTracePhysicalPairedBranches
      4 (by norm_num) (by norm_num) := by
  apply sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps
    4 (by norm_num) (by norm_num)
  · intro n hn0 hn4
    simpa using
      sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors
        n hn0 hn4
  · exact hsteps


theorem
    sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings
    (hroutes :
      SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings
        4 (by norm_num) (by norm_num)) :
    SixVertexPositiveEvenTracePhysicalPairedBranches
      4 (by norm_num) (by norm_num) := by
  apply sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings
    4 (by norm_num) (by norm_num)
  · intro n hn0 hn4
    simpa using
      sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors
        n hn0 hn4
  · exact hroutes


theorem sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 1 <= c)
    (hbranches : SixVertexPositiveEvenTracePhysicalPairedBranches
      N hNpos hNeven) :
    SixVertexSectorPositiveEvenTraceLogConcave N c := by
  intro M n hn0 hnN
  let T := sixVertexPositiveEvenTorus N M hNpos hNeven
  let middle : Fin (T.width + 1) :=
    ⟨n, by simp [T, sixVertexPositiveEvenTorus]; omega⟩
  obtain ⟨embeddings⟩ := hbranches M n hn0 hnN
  simpa [T, middle, sixVertexPositiveEvenTorus] using
    (sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      T middle hn0 hnN hc embeddings)


theorem sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 1 <= c)
    (hbranches : SixVertexPositiveEvenTracePhysicalPairedBranches
      N hNpos hNeven) :
    SixVertexSectorPerronLogConcave N c :=
  sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave N
    (lt_of_lt_of_le Real.zero_lt_one hc)
    (sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches
      N hNpos hNeven hc hbranches)


end
end StatMech.FrontierD
