import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part5
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexConfigurationPairUnionCyclePairedRepairs


/--
[sixVertexPairAtMostTwoCycleFineRelated_swap_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleFineRelated_swap_target_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated source (target.2, target.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleFineRelated_swap_target hrelated

/--
[sixVertexSwapPhysicalTarget_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexSwapPhysicalTarget_swap_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {target : SixVertexConfigurationPhysicalTarget T middle} :
-- imply
  sixVertexSwapPhysicalTarget (sixVertexSwapPhysicalTarget target) = target := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapPhysicalTarget_swap target

/--
[sixVertexSwapPhysicalTarget_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexSwapPhysicalTarget_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)} :
-- imply
  Function.Injective (sixVertexSwapPhysicalTarget (T := T) (middle := middle)) := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapPhysicalTarget_injective

/--
[target_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma target_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle hmiddle_pos hmiddle_lt}
  (source)
  (branch) :
-- imply
  sixVertexConfigurationPairTotalCPhysical (repairs.target source branch) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairUnionCyclePairedRepairs.target_totalC repairs

/--
[twoCycleFineHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma twoCycleFineHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle hmiddle_pos hmiddle_lt} :
-- imply
  SixVertexConfigurationPairTwoCycleFineHall T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairUnionCyclePairedRepairs.twoCycleFineHall repairs

/--
[markedTraceCoefficientwiseLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma markedTraceCoefficientwiseLogConcave_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle hmiddle_pos hmiddle_lt} :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairUnionCyclePairedRepairs.markedTraceCoefficientwiseLogConcave repairs

/--
[pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings_eq
  {N : Nat}
  {hNpos : 0 < N}
  {hNeven : Even N}
-- given
  (hembeddings : SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings N hNpos hNeven) :
-- imply
  SixVertexPositiveEvenTracePairUnionCyclePairedRepairs N hNpos hNeven := by
-- proof
  apply StatMech.FrontierD.pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings hembeddings

/--
[canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings_eq
-- given
  (hembeddings : SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings) :
-- imply
  SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs := by
-- proof
  apply StatMech.FrontierD.canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings hembeddings

/--
[sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs_eq
  {N : Nat}
  {c : Real}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hc : 2 ≤ c)
  (hrepairs : SixVertexPositiveEvenTracePairUnionCyclePairedRepairs N hNpos hNeven) :
-- imply
  SixVertexSectorPositiveEvenTraceLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs N hNpos hNeven hc hrepairs

/--
[sixVertexSectorPerronLogConcave_of_pairUnionCyclePairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexSectorPerronLogConcave_of_pairUnionCyclePairedRepairs_eq
  {N : Nat}
  {c : Real}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hc : 2 ≤ c)
  (hrepairs : SixVertexPositiveEvenTracePairUnionCyclePairedRepairs N hNpos hNeven) :
-- imply
  SixVertexSectorPerronLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronLogConcave_of_pairUnionCyclePairedRepairs N hNpos hNeven hc hrepairs

/--
[canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs_eq
-- given
  (hrepairs : SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs) :
-- imply
  SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
-- proof
  apply StatMech.FrontierD.canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs hrepairs

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : ∀ scale k : Nat, 0 < scale → Even scale → 12 * scale + 2 < 2 * (k + 3) → ∀ᶠ blocks in Filter.atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hrepairs : SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs hq hhard hcross hrepairs

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCycleOffDiagonalEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCycleOffDiagonalEmbeddings_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : ∀ scale k : Nat, 0 < scale → Even scale → 12 * scale + 2 < 2 * (k + 3) → ∀ᶠ blocks in Filter.atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hembeddings : SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCycleOffDiagonalEmbeddings hq hhard hcross hembeddings

/--
[sixVertexFourByTwoMatchingTable_layers_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingTable_layers_ne_eq
  {i : Fin 200} :
-- imply
  (sixVertexFourByTwoMatchingTable i).1 ≠ (sixVertexFourByTwoMatchingTable i).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingTable_layers_ne i

/--
[sixVertexFourByTwoConfigurationPairMatching_layers_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoConfigurationPairMatching_layers_ne_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo} :
-- imply
  (sixVertexFourByTwoConfigurationPairMatching source).1 ≠ (sixVertexFourByTwoConfigurationPairMatching source).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoConfigurationPairMatching_layers_ne source


-- created on 2026-10-23
