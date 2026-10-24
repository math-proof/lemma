import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSpliceReconnection StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection


/--
[sixVertexLoopDecoratedSpliceUnitTarget_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedSpliceUnitTarget_colored_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey (sixVertexLoopDecoratedPairColored source)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt source key) = key.splice.target := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedSpliceUnitTarget_colored middle hmiddle_pos hmiddle_lt source key

/--
[sixVertexLoopDecoratedSpliceUnitTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedSpliceUnitTarget_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey (sixVertexLoopDecoratedPairColored source)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexLoopDecoratedPairBigrade (sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt source key) = sixVertexLoopDecoratedPairBigrade source := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedSpliceUnitTarget_bigrade middle hmiddle_pos hmiddle_lt source key

/--
[sixVertexHorizontalDegreeTwoLoopSpliceTarget_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopSpliceTarget_val_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey (sixVertexLoopDecoratedPairColored source.1)} :
-- imply
  (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1 = sixVertexLoopDecoratedSpliceUnitTarget middle hmiddle_pos hmiddle_lt source.1 key := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopSpliceTarget_val source key

/--
[sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey (sixVertexLoopDecoratedPairColored source.1)} :
-- imply
  SixVertexConfigurationPairTwoCycleFineRelated source.1.1 (sixVertexHorizontalDegreeTwoLoopSpliceTarget source key).1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source key

/--
[sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  FKColoredFineTwoCycleUnitTransferSpliceKey.SourceSeamDifferenceTwo (sixVertexLoopDecoratedPairColored source.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopSource_seamDifferenceTwo source

/--
[branchKey_true_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma branchKey_true_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  (targets.branchKey source true).splice.target = fkColoredLoopPairingPairSwapLayers (targets.branchKey source false).splice.target := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.branchKey_true_target targets source

/--
[target_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma target_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1 (targets.branchKey source false) ≠ sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1 (targets.branchKey source true) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.target_distinct targets source

/--
[target_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma target_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  Function.Injective (fun source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade => sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1 (targets.branchKey source branch)) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.target_injective targets branch

/--
[paired_inverse_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma paired_inverse_spec_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade}
  {source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade // targets.PairedRelated source target}} :
-- imply
  sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1.1 (targets.branchKey source.1 (targets.pairedInverseBranch target source)) = target := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.paired_inverse_spec targets target source

/--
[paired_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma paired_source_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  2 ≤ (Finset.univ.filter (targets.PairedRelated source)).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.paired_source_degree targets source

/--
[paired_inverse_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma paired_inverse_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade} :
-- imply
  (Finset.univ.filter fun source => targets.PairedRelated source target).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.paired_inverse_degree targets target

/--
[paired_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma paired_hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  ∀ sources : Finset (SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade), sources.card ≤ (Finset.univ.filter fun target => ∃ source, source ∈ sources ∧ targets.PairedRelated source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.paired_hall targets

/--
[pairedMatching_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma pairedMatching_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective targets.pairedMatching := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.pairedMatching_injective targets

/--
[pairedMatching_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma pairedMatching_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  (source) :
-- imply
  targets.PairedRelated source (targets.pairedMatching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.pairedMatching_related targets

/--
[pairedMatching_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma pairedMatching_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {targets : SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  SixVertexConfigurationPairTwoCycleFineRelated source.1.1.1 (targets.pairedMatching source).1.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets.pairedMatching_supported targets source

/--
[reconnect_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma reconnect_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  SixVertexConfigurationPairTwoCycleFineRelated source.1.1 (reconnection.reconnect source).1.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSpliceReconnection.reconnect_supported reconnection source

/--
[reconnect_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma reconnect_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective reconnection.reconnect := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopSpliceReconnection.reconnect_injective reconnection

/--
[decode_high_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma decode_high_matching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  decoded.decode (decoded.high.pairedMatching source) = some source.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection.decode_high_matching decoded source

/--
[loopBigradeFibers_of_degreeTwoLoopSpliceReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma loopBigradeFibers_of_degreeTwoLoopSpliceReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hreconnections : SixVertexHorizontalDegreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexLoopDecoratedPairBigradeFiberDominates T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle := by
-- proof
  apply StatMech.FrontierD.loopBigradeFibers_of_degreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt hreconnections

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hreconnections : SixVertexHorizontalDegreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt hreconnections

/--
[degreeTwoLoopSpliceReconnections_of_decoded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma degreeTwoLoopSpliceReconnections_of_decoded_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalDegreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.degreeTwoLoopSpliceReconnections_of_decoded T middle hmiddle_pos hmiddle_lt hdecoded

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopDecodedSpliceReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopDecodedSpliceReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopDecodedSpliceReconnections T middle hmiddle_pos hmiddle_lt hdecoded

/--
[degreeTwoLoopSpliceReconnections_of_selectedOutputDecoders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma degreeTwoLoopSpliceReconnections_of_selectedOutputDecoders_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoders T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalDegreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.degreeTwoLoopSpliceReconnections_of_selectedOutputDecoders T middle hmiddle_pos hmiddle_lt hdecoded

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputDecoders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputDecoders_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoders T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputDecoders T middle hmiddle_pos hmiddle_lt hdecoded

/--
[degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalDegreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.degreeTwoLoopSpliceReconnections_of_selectedOutputResolvedCrossDecoders T middle hmiddle_pos hmiddle_lt hdecoded

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputResolvedCrossDecoders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputResolvedCrossDecoders_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputResolvedCrossDecoders T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputResolvedCrossDecoders T middle hmiddle_pos hmiddle_lt hdecoded

/--
[degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalDegreeTwoLoopSpliceReconnections T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.degreeTwoLoopSpliceReconnections_of_selectedOutputFullMaskDecoders T middle hmiddle_pos hmiddle_lt hdecoded

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputFullMaskDecoders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputFullMaskDecoders_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoders T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopSelectedOutputFullMaskDecoders T middle hmiddle_pos hmiddle_lt hdecoded


-- created on 2026-10-23
