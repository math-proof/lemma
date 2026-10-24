import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch
open Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoMatchingTable_components_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingTable_components_ne_eq
  {i : Fin 200} :
-- imply
  (sixVertexFourByTwoMatchingTable i).1 ≠ (sixVertexFourByTwoMatchingTable i).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingTable_components_ne i

/--
[sixVertexFourByTwoMatchingIndex_components_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingIndex_components_ne_eq
  {i : Fin 4 × Fin 50} :
-- imply
  (sixVertexFourByTwoMatchingIndex i).1 ≠ (sixVertexFourByTwoMatchingIndex i).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingIndex_components_ne i

/--
[sixVertexFourByTwoConfigurationPairMatching_components_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoConfigurationPairMatching_components_ne_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo} :
-- imply
  (sixVertexFourByTwoConfigurationPairMatching source).1 ≠ (sixVertexFourByTwoConfigurationPairMatching source).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoConfigurationPairMatching_components_ne source

/--
[sixVertexFourByTwoPhysicalBranch_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoPhysicalBranch_distinct_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo} :
-- imply
  sixVertexFourByTwoPhysicalBranch false source ≠ sixVertexFourByTwoPhysicalBranch true source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoPhysicalBranch_distinct source

/--
[sixVertexFourByTwoPhysicalBranch_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoPhysicalBranch_totalC_eq
  {choice : Bool}
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoPhysicalBranch choice source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoPhysicalBranch_totalC choice source

/--
[sixVertexFourByTwoSectorOne_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOne_pos_eq :
-- imply
  0 < sixVertexFourByTwoSectorOne.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOne_pos

/--
[sixVertexFourByTwoSectorOne_lt_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOne_lt_width_eq :
-- imply
  sixVertexFourByTwoSectorOne.val < sixVertexFourByTwoTorus.width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOne_lt_width

/--
[sixVertexFourByTwoPhysicalSourceEmbedding_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoPhysicalSourceEmbedding_totalC_eq
  {source : SixVertexConfigurationPhysicalSource sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne_pos sixVertexFourByTwoSectorOne_lt_width} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoPhysicalSourceEmbedding source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoPhysicalSourceEmbedding_totalC source

/--
[sixVertexFourByTwo_sectorTrace_logConcave_of_physicalBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwo_sectorTrace_logConcave_of_physicalBranches_eq
  {c : Real}
-- given
  (hc : 1 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 0 c ^ 2) * Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) <= Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_sectorTrace_logConcave_of_physicalBranches hc

/--
[sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_eq :
-- imply
  Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num)) ⟨1, by norm_num [sixVertexPositiveEvenTorus]⟩ (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches

/--
[sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches_eq :
-- imply
  Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num)) ⟨2, by norm_num [sixVertexPositiveEvenTorus]⟩ (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches

/--
[sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches_eq :
-- imply
  Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num)) ⟨3, by norm_num [sixVertexPositiveEvenTorus]⟩ (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches

/--
[sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors_eq
  {n : Nat}
-- given
  (hn0 : 0 < n)
  (hn4 : n < 4) :
-- imply
  Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num)) ⟨n, by norm_num [sixVertexPositiveEvenTorus]; omega⟩ hn0 hn4) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors n hn0 hn4

/--
[sixVertexFour_twoRowCommonFactor_cardinality_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFour_twoRowCommonFactor_cardinality_obstruction_eq :
-- imply
  ¬ ∃ factor : Nat, (4 * 50) * factor = 16 * 1682 ∧ (28 * 28) * factor = 628 * 628 := by
-- proof
  apply StatMech.FrontierD.sixVertexFour_twoRowCommonFactor_cardinality_obstruction

/--
[sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps_eq
  {N : Nat}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hbase : forall n : Nat, (hn0 : 0 < n) -> (hnN : n < N) -> Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings (sixVertexPositiveEvenTorus N 0 hNpos hNeven) ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN))
  (hsteps : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations N hNpos hNeven) :
-- imply
  SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps N hNpos hNeven hbase hsteps

/--
[sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings_eq
  {N : Nat}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hbase : forall n : Nat, (hn0 : 0 < n) -> (hnN : n < N) -> Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings (sixVertexPositiveEvenTorus N 0 hNpos hNeven) ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN))
  (hroutes : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings N hNpos hNeven) :
-- imply
  SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings N hNpos hNeven hbase hroutes

/--
[sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightSteps_eq
-- given
  (hsteps : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations 4 (by norm_num) (by norm_num)) :
-- imply
  SixVertexPositiveEvenTracePhysicalPairedBranches 4 (by norm_num) (by norm_num) := by
-- proof
  apply StatMech.FrontierD.sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightSteps hsteps

/--
[sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings_eq
-- given
  (hroutes : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings 4 (by norm_num) (by norm_num)) :
-- imply
  SixVertexPositiveEvenTracePhysicalPairedBranches 4 (by norm_num) (by norm_num) := by
-- proof
  apply StatMech.FrontierD.sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings hroutes

/--
[sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches_eq
  {N : Nat}
  {c : Real}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hc : 1 <= c)
  (hbranches : SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven) :
-- imply
  SixVertexSectorPositiveEvenTraceLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches N hNpos hNeven hc hbranches

/--
[sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches_eq
  {N : Nat}
  {c : Real}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hc : 1 <= c)
  (hbranches : SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven) :
-- imply
  SixVertexSectorPerronLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches N hNpos hNeven hc hbranches

/--
[tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hbranches : SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches) :
-- imply
  Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches hq r hbranches

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hbranches : SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches hq hhard hcross hbranches


-- created on 2026-10-23
