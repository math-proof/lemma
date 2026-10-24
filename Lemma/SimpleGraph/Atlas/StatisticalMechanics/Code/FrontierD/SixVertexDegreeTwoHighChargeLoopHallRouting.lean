import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting
open Finset StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets


/--
[sixVertexLoopDecoratedPairColored_slotColor_eq_degreeTwoAligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_slotColor_eq_degreeTwoAligned_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T left right}
  {slot : FKLayeredStrandSlot T}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1) :
-- imply
  fkColoredLayeredSlotColor (sixVertexLoopDecoratedPairColored source) slot = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1 source.1.2.2.1 hdegree) slot := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_slotColor_eq_degreeTwoAligned source hdegree slot

/--
[sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma rebaseToLoopDecoration_target_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T left right}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1 source.1.2.2.1 hdegree)}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1) :
-- imply
  (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration source hdegree key).splice.target = key.splice.target := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration_target source hdegree key

/--
[sixVertexHorizontalDegreeTwoLoopHighChargeComponent_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopHighChargeComponent_charge_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge source.1.1.1.1.2.1 source.1.1.1.2.2.1 (sixVertexHorizontalDegreeTwoLoopHighChargeDegree source) (sixVertexHorizontalDegreeTwoLoopHighChargeComponent source) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopHighChargeComponent_charge source

/--
[sixVertexHorizontalDegreeTwoLoopRoutedTarget_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopRoutedTarget_val_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexLoopDecoratedPairColored source.1)} :
-- imply
  (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1 = sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos hmiddle_lt source.1 key := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopRoutedTarget_val source key

/--
[sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexLoopDecoratedPairColored source.1)} :
-- imply
  SixVertexConfigurationPairTwoCycleFineRelated source.1.1 (sixVertexHorizontalDegreeTwoLoopRoutedTarget source key).1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported source key

/--
[routedKey_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma routedKey_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  (targets.routedKey source branch).splice.target = ((targets.paired source).key branch).splice.target := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets.routedKey_target targets source branch

/--
[routedTarget_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma routedTarget_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (targets.routedKey source false) ≠ sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (targets.routedKey source true) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets.routedTarget_distinct targets source

/--
[routedTarget_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma routedTarget_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  Function.Injective (fun source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade => sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (targets.routedKey source branch)) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedPairedTargets.routedTarget_injective targets branch

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_branch_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma paired_branch_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  (branch) :
-- imply
  Function.Injective (fun source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade => sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (reconnection.key source.1 branch)) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_branch_injective reconnection

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma paired_inverse_spec_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade}
  {source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade // reconnection.PairedRelated source target}} :
-- imply
  sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1.1 (reconnection.key source.1.1 (reconnection.pairedInverseBranch target source)) = target := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_spec reconnection target source

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.output_recovers_occurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma output_recovers_occurrence_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  (branch)
  {first second : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
-- given
  (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first.1 (reconnection.key first.1 branch) = sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1 (reconnection.key second.1 branch)) :
-- imply
  sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv first = sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv second := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.output_recovers_occurrence reconnection first second heq

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma paired_source_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  2 ≤ (Finset.univ.filter (reconnection.PairedRelated source)).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_source_degree reconnection source

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma paired_inverse_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade} :
-- imply
  (Finset.univ.filter fun source => reconnection.PairedRelated source target).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_degree reconnection target

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma paired_hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  ∀ sources : Finset (SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade), sources.card ≤ (Finset.univ.filter fun target => ∃ source, source ∈ sources ∧ reconnection.PairedRelated source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_hall reconnection

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma pairedMatching_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective reconnection.pairedMatching := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_injective reconnection

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma pairedMatching_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  (source) :
-- imply
  reconnection.PairedRelated source (reconnection.pairedMatching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_related reconnection

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma reconnect_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  SixVertexConfigurationPairTwoCycleFineRelated source.1.1 (reconnection.reconnect source).1.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_supported reconnection source

/--
[SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma reconnect_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective reconnection.reconnect := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_injective reconnection

/--
[loopBigradeFibers_of_degreeTwoLoopRoutedReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma loopBigradeFibers_of_degreeTwoLoopRoutedReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hreconnections : SixVertexHorizontalDegreeTwoLoopRoutedReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexLoopDecoratedPairBigradeFiberDominates T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle := by
-- proof
  apply StatMech.FrontierD.loopBigradeFibers_of_degreeTwoLoopRoutedReconnections T middle hmiddle_pos hmiddle_lt hreconnections

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hreconnections : SixVertexHorizontalDegreeTwoLoopRoutedReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections T middle hmiddle_pos hmiddle_lt hreconnections


-- created on 2026-10-23
