import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourAuditedCoordinateTargetPair_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateTargetPair_valid_eq
  {c : SixVertexFourByFourAuditedCoordinates} :
-- imply
  SixVertexFourByFourAuditedCoordinateTargetPairValid c := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateTargetPair_valid c

/--
[sixVertexFourByFourAuditedCoordinate_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinate_fineRelated_eq
  {c : SixVertexFourByFourAuditedCoordinates} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByFourAuditedCoordinateSourcePair c) (sixVertexFourByFourAuditedCoordinateTargetPair c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinate_fineRelated c

/--
[sixVertexFourByFourRowOfMask_injective_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourRowOfMask_injective_of_lt_eq
  {a b : Nat}
-- given
  (ha : a < 16)
  (hb : b < 16)
  (hrow : sixVertexFourByFourRowOfMask a = sixVertexFourByFourRowOfMask b) :
-- imply
  a = b := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourRowOfMask_injective_of_lt ha hb hrow

/--
[sixVertexFourByFourAuditedRowZero_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedRowZero_lt_eq
  {p : Fin 16} :
-- imply
  (sixVertexFourByFourAuditedRowZero p).1 < 16 /\ (sixVertexFourByFourAuditedRowZero p).2 < 16 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedRowZero_lt p

/--
[sixVertexFourByFourAuditedRowMiddle_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedRowMiddle_lt_eq
  {p : Fin 16} :
-- imply
  (sixVertexFourByFourAuditedRowMiddle p).1 < 16 /\ (sixVertexFourByFourAuditedRowMiddle p).2 < 16 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedRowMiddle_lt p

/--
[sixVertexFourByFourAuditedRowLast_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedRowLast_lt_eq
  {p : Fin 4} :
-- imply
  (sixVertexFourByFourAuditedRowLast p).1 < 16 /\ (sixVertexFourByFourAuditedRowLast p).2 < 16 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedRowLast_lt p

/--
[sixVertexFourByFourAuditedRowZero_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedRowZero_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedRowZero := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedRowZero_injective

/--
[sixVertexFourByFourAuditedRowMiddle_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedRowMiddle_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedRowMiddle := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedRowMiddle_injective

/--
[sixVertexFourByFourAuditedRowLast_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedRowLast_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedRowLast := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedRowLast_injective

/--
[sixVertexFourByFourAuditedCoordinateRowZero_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateRowZero_injective_eq :
-- imply
  Function.Injective (fun s : Fin 4 × Fin 4 => sixVertexFourByFourAuditedCoordinateRowZero s.1 s.2) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateRowZero_injective

/--
[sixVertexFourByFourAuditedMiddlePair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedMiddlePair_injective_eq
  {firstSeam secondSeam : Fin 4} :
-- imply
  Function.Injective (sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedMiddlePair_injective firstSeam secondSeam

/--
[sixVertexFourByFourAuditedCoordinateHorizontalRows_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateHorizontalRows_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedCoordinateHorizontalRows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateHorizontalRows_injective

/--
[sixVertexFourByFourAuditedCoordinateTargetPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateTargetPair_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedCoordinateTargetPair := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateTargetPair_injective

/--
[sixVertexFourByFourAuditedCoordinateSourcePair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateSourcePair_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedCoordinateSourcePair := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateSourcePair_injective

/--
[sixVertexFourByFourAuditedCoordinate_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinate_matching_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedCoordinateSourcePair /\ Function.Injective sixVertexFourByFourAuditedCoordinateTargetPair /\ forall c, SixVertexFourByFourAuditedCoordinateSourcePairValid c /\ SixVertexFourByFourAuditedCoordinateTargetPairValid c /\ sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByFourAuditedCoordinateSourcePair c) (sixVertexFourByFourAuditedCoordinateTargetPair c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinate_matching

/--
[sixVertexFourByFourAuditedCoordinateParameters_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateParameters_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedCoordinateParameters := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateParameters_injective

/--
[sixVertexFourByFourAuditedCoordinates_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinates_card_eq :
-- imply
  Fintype.card SixVertexFourByFourAuditedCoordinates = 512 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinates_card

/--
[sixVertexFourByFourAuditedHorizontalParameters_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedHorizontalParameters_card_eq :
-- imply
  Fintype.card SixVertexFourByFourAuditedHorizontalParameters = 16384 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedHorizontalParameters_card

/--
[sixVertexFourByFourAuditedCoordinateParameterImage_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateParameterImage_card_eq :
-- imply
  sixVertexFourByFourAuditedCoordinateParameterImage.card = 512 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateParameterImage_card

/--
[sixVertexFourByFourAuditedCoordinateParameterComplement_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateParameterComplement_card_eq :
-- imply
  sixVertexFourByFourAuditedCoordinateParameterComplement.card = 15872 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateParameterComplement_card


-- created on 2026-10-23
