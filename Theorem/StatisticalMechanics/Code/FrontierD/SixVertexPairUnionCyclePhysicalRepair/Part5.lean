/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part4


namespace StatMech.FrontierD

noncomputable section

theorem pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
    {N : Nat} {hNpos : 0 < N} {hNeven : Even N}
    (hembeddings :
      SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings
        N hNpos hNeven) :
    SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      N hNpos hNeven := by
  intro M n hn0 hnN
  obtain ⟨embedding⟩ := hembeddings M n hn0 hnN
  exact ⟨embedding.toPairedRepairs⟩

theorem canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
    (hembeddings :
      SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings) :
    SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs := by
  intro r k
  exact pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
    (hembeddings r k)


theorem sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 2 ≤ c)
    (hrepairs : SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      N hNpos hNeven) :
    SixVertexSectorPositiveEvenTraceLogConcave N c := by
  intro M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs M n hn0 hnN
  let T := sixVertexPositiveEvenTorus N M hNpos hNeven
  let middle : Fin (T.width + 1) :=
    ⟨n, by simp [T, sixVertexPositiveEvenTorus]; omega⟩
  simpa [T, middle, sixVertexPositiveEvenTorus] using
    sixVertexSectorTrace_logConcave_of_twoCycleFineHall
      T middle hn0 hnN hc repairs.twoCycleFineHall

theorem sixVertexSectorPerronLogConcave_of_pairUnionCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 2 ≤ c)
    (hrepairs : SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      N hNpos hNeven) :
    SixVertexSectorPerronLogConcave N c :=
  sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave N
    (by linarith)
    (sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs
      N hNpos hNeven hc hrepairs)

theorem canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs
    (hrepairs :
      SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs) :
    SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
  intro r k M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs r k M n hn0 hnN
  exact ⟨repairs.toPhysicalPairedBranches⟩

theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : ∀ scale k : Nat,
      0 < scale → Even scale →
      12 * scale + 2 < 2 * (k + 3) →
      ∀ᶠ blocks in Filter.atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hrepairs :
      SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
    hq hhard hcross
      (canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs hrepairs)


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCycleOffDiagonalEmbeddings
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : ∀ scale k : Nat,
      0 < scale → Even scale →
      12 * scale + 2 < 2 * (k + 3) →
      ∀ᶠ blocks in Filter.atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hembeddings :
      SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs
    hq hhard hcross
      (canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
        hembeddings)


set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoMatchingTable_layers_ne (i : Fin 200) :
    (sixVertexFourByTwoMatchingTable i).1 ≠
      (sixVertexFourByTwoMatchingTable i).2 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoConfigurationPairMatching_layers_ne
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    (sixVertexFourByTwoConfigurationPairMatching source).1 ≠
      (sixVertexFourByTwoConfigurationPairMatching source).2 := by
  intro heq
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hindex :
      (sixVertexFourByTwoMatchingIndex i).1 =
        (sixVertexFourByTwoMatchingIndex i).2 := by
    apply sixVertexFourByTwoSectorOneConfiguration_injective
    exact heq
  apply sixVertexFourByTwoMatchingTable_layers_ne
    (finProdFinEquiv (m := 4) (n := 50) i)
  exact hindex


end
end StatMech.FrontierD
