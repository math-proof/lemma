import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexPositiveUnitComponentResidualOrbitCover StatMech.FrontierD.SixVertexHorizontalResidualGeometricCertificate StatMech.FrontierD.SixVertexHorizontalResidualHighGeometricSurplusRepair StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting


/--
[SixVertexPositiveUnitComponentResidualWitness.degreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma degreeTwo_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHallSource T middle hmiddle_pos hmiddle_lt grade}
  {witness : SixVertexPositiveUnitComponentResidualWitness source} :
-- imply
  SixVertexLocallyDegreeTwo (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1 (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualWitness.degreeTwo witness

/--
[positiveUnitComponentResidualTargetLift_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma positiveUnitComponentResidualTargetLift_nonempty_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {physical : SixVertexPositiveUnitComponentOrbitCover T middle hmiddle_pos hmiddle_lt (SixVertexPositiveUnitComponentResidualSources T middle hmiddle_pos hmiddle_lt grade)}
-- given
  (hcoverage : SixVertexPositiveUnitComponentResidualTargetCoverage physical) :
-- imply
  Nonempty {lift : (Σ index, (physical.data index).TargetLayer) ↪ SixVertexHorizontalDegreeTwoHallTarget T middle hmiddle_pos hmiddle_lt grade // ∀ index target, sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding T middle hmiddle_pos hmiddle_lt grade (lift ⟨index, target⟩) = physical.targetEmbedding ⟨index, target⟩} := by
-- proof
  apply StatMech.FrontierD.positiveUnitComponentResidualTargetLift_nonempty physical hcoverage

/--
[matching_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma matching_physical_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexPositiveUnitComponentResidualSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding T middle hmiddle_pos hmiddle_lt grade (cover.matching source) = cover.physical.matching source := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualOrbitCover.matching_physical cover source

/--
[matching_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma matching_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentResidualOrbitCover T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexPositiveUnitComponentResidualSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source.1 (cover.matching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualOrbitCover.matching_supported cover source

/--
[sixVertexHorizontalHallSourceCanonicalLoop_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalHallSourceCanonicalLoop_pair_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHallSource T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  (sixVertexHorizontalHallSourceCanonicalLoop source).1.1 = (sixVertexHorizontalActualDeficitConfigurationPair source).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalHallSourceCanonicalLoop_pair source

/--
[sixVertexHorizontalHallTargetCanonicalLoop_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalHallTargetCanonicalLoop_pair_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {target : SixVertexHorizontalDegreeTwoHallTarget T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  (sixVertexHorizontalHallTargetCanonicalLoop target).1.1 = (sixVertexHorizontalActualSurplusConfigurationPair target).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalHallTargetCanonicalLoop_pair target

/--
[loopTarget_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma loopTarget_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {certificate : SixVertexHorizontalResidualGeometricCertificate source} :
-- imply
  SixVertexConfigurationPairTwoCycleFineRelated source.1.1 certificate.loopTarget.1.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalResidualGeometricCertificate.loopTarget_supported certificate

/--
[SixVertexHorizontalResidualGeometricSurplusRepair.supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHallSource T middle hmiddle_pos hmiddle_lt grade}
  {repair : SixVertexHorizontalResidualGeometricSurplusRepair source} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source repair.target := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalResidualGeometricSurplusRepair.supported repair

/--
[target_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma target_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {repair : SixVertexHorizontalResidualHighGeometricSurplusRepair source}
  {branch : Bool} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source.1 (repair.target branch) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalResidualHighGeometricSurplusRepair.target_supported repair branch

/--
[target_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma target_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {repair : SixVertexHorizontalResidualHighGeometricSurplusRepair source} :
-- imply
  repair.target false ≠ repair.target true := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalResidualHighGeometricSurplusRepair.target_distinct repair

/--
[paired_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma paired_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  routing.paired source false ≠ routing.paired source true := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.paired_distinct routing source

/--
[paired_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma paired_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source.1 (routing.paired source branch) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.paired_supported routing source branch

/--
[paired_output_recovers_occurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma paired_output_recovers_occurrence_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool}
  {first second : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
-- given
  (heq : routing.paired first branch = routing.paired second branch) :
-- imply
  sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first = sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.paired_output_recovers_occurrence routing branch first second heq

/--
[paired_injective_with_occurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma paired_injective_with_occurrence_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool}
  {first second : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
-- given
  (_ : sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first = sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second)
  (heq : routing.paired first branch = routing.paired second branch) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.paired_injective_with_occurrence routing branch first second _ heq

/--
[geometric_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma geometric_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective (fun source => (routing.geometric source).target) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.geometric_injective routing

/--
[geometric_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma geometric_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexPositiveUnitComponentResidualGeometricSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source.1 (routing.geometric source).target := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.geometric_supported routing source

/--
[unit_paired_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma unit_paired_disjoint_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {unitSource : SixVertexPositiveUnitComponentResidualSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool}
-- given
  (highSource : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade) :
-- imply
  routing.unit.matching unitSource ≠ routing.paired highSource branch := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.unit_paired_disjoint routing unitSource highSource branch

/--
[decode_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma decode_direct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  routing.decoder (routing.direct source) = some source.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.decode_direct routing source

/--
[direct_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma direct_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source.1 (routing.direct source) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.direct_supported routing source

/--
[direct_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma direct_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective routing.direct := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.direct_injective routing

/--
[direct_paired_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma direct_paired_disjoint_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle hmiddle_pos hmiddle_lt grade}
  {directSource : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
  {pairedSource : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  routing.direct directSource ≠ routing.paired pairedSource branch := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentResidualMixedRouting.direct_paired_disjoint routing directSource pairedSource branch

/--
[offDiagonalTwoCycleMatching_of_positiveUnitComponentMixedRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_of_positiveUnitComponentMixedRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexPositiveUnitComponentResidualMixedRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_of_positiveUnitComponentMixedRoutings T middle hmiddle_pos hmiddle_lt hroutings

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_positiveUnitComponentMixedRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_positiveUnitComponentMixedRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexPositiveUnitComponentResidualMixedRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_positiveUnitComponentMixedRoutings T middle hmiddle_pos hmiddle_lt hroutings


-- created on 2026-10-23
