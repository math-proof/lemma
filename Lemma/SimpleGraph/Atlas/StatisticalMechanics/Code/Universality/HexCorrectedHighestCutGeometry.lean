import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry.Part3
open StatMech StatMech.Universality StatMech.Universality.HexCSCutData


/--
[hexCS_endpoint_dropLast_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma hexCS_endpoint_dropLast_isLegalSAW_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hne : ts ≠ [])
  (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW) :
-- imply
  (ofTurns a h0 ts.dropLast).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexCS_endpoint_dropLast_isLegalSAW a h0 ts hne hlegal

/--
[hexCSCutPrefixOutput_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma hexCSCutPrefixOutput_ne_nil_eq
  {pre : List ℤ}
  {cutTurn : ℤ} :
-- imply
  hexCSCutPrefixOutput pre cutTurn ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSCutPrefixOutput_ne_nil pre cutTurn

/--
[hexCSCutSuffixOutput_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma hexCSCutSuffixOutput_ne_nil_eq
  {entryTurn : ℤ}
  {suffix : List ℤ}
  {finalTurn : ℤ} :
-- imply
  hexCSCutSuffixOutput entryTurn suffix finalTurn ≠ [] := by
-- proof
  apply StatMech.Universality.hexCSCutSuffixOutput_ne_nil entryTurn suffix finalTurn

/--
[hexCSDecodeCutPair_encode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma hexCSDecodeCutPair_encode_eq
  {pre : List ℤ}
  {cutTurn entryTurn : ℤ}
  {suffix : List ℤ}
  {finalTurn : ℤ} :
-- imply
  hexCSDecodeCutPair (hexCSCutPrefixOutput pre cutTurn, hexCSCutSuffixOutput entryTurn suffix finalTurn) = pre ++ [cutTurn] ++ suffix ++ [finalTurn] := by
-- proof
  apply StatMech.Universality.hexCSDecodeCutPair_encode pre cutTurn entryTurn suffix finalTurn

/--
[hexCSCutPair_source_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma hexCSCutPair_source_eq_eq
  {pre pre' : List ℤ}
  {cutTurn cutTurn' : ℤ}
  {entryTurn entryTurn' : ℤ}
  {suffix suffix' : List ℤ}
  {finalTurn finalTurn' : ℤ}
-- given
  (hpair : (hexCSCutPrefixOutput pre cutTurn, hexCSCutSuffixOutput entryTurn suffix finalTurn) = (hexCSCutPrefixOutput pre' cutTurn', hexCSCutSuffixOutput entryTurn' suffix' finalTurn')) :
-- imply
  pre ++ [cutTurn] ++ suffix ++ [finalTurn] = pre' ++ [cutTurn'] ++ suffix' ++ [finalTurn'] := by
-- proof
  apply StatMech.Universality.hexCSCutPair_source_eq hpair

/--
[hexCSCutPair_length_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma hexCSCutPair_length_add_one_eq
  {pre : List ℤ}
  {cutTurn entryTurn : ℤ}
  {suffix : List ℤ}
  {finalTurn : ℤ} :
-- imply
  (hexCSCutPrefixOutput pre cutTurn).length + (hexCSCutSuffixOutput entryTurn suffix finalTurn).length = (pre ++ [cutTurn] ++ suffix ++ [finalTurn]).length + 1 := by
-- proof
  apply StatMech.Universality.hexCSCutPair_length_add_one pre cutTurn entryTurn suffix finalTurn

/--
[decode_outputPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma decode_outputPair_eq
  {W : ℕ}
  {hW : 0 < W}
  {source : List ℤ}
  {D : HexCSCutData W hW source} :
-- imply
  hexCSDecodeCutPair D.outputPair = source := by
-- proof
  apply StatMech.Universality.HexCSCutData.decode_outputPair D

/--
[output_length_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean)
-/
@[path]
private lemma output_length_add_one_eq
  {W : ℕ}
  {hW : 0 < W}
  {source : List ℤ}
  {D : HexCSCutData W hW source} :
-- imply
  D.outputPair.1.length + D.outputPair.2.length = source.length + 1 := by
-- proof
  apply StatMech.Universality.HexCSCutData.output_length_add_one D


-- created on 2026-10-23
