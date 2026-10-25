/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Def.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hexCSCutPrefixOutput_ne_nil
    (pre : List ℤ) (cutTurn : ℤ) :
    hexCSCutPrefixOutput pre cutTurn ≠ [] := by
  simp [hexCSCutPrefixOutput]

@[simp] theorem hexCSCutSuffixOutput_ne_nil
    (entryTurn : ℤ) (suffix : List ℤ) (finalTurn : ℤ) :
    hexCSCutSuffixOutput entryTurn suffix finalTurn ≠ [] := by
  simp [hexCSCutSuffixOutput]


@[simp] theorem hexCSDecodeCutPair_encode
    (pre : List ℤ) (cutTurn entryTurn : ℤ)
    (suffix : List ℤ) (finalTurn : ℤ) :
    hexCSDecodeCutPair
        (hexCSCutPrefixOutput pre cutTurn,
          hexCSCutSuffixOutput entryTurn suffix finalTurn) =
      pre ++ [cutTurn] ++ suffix ++ [finalTurn] := by
  unfold hexCSDecodeCutPair hexCSCutPrefixOutput hexCSCutSuffixOutput
  rw [List.dropLast_concat, List.getLastD_concat,
    List.dropLast_concat, List.getLastD_concat]
  simp


theorem hexCSCutPair_source_eq
    {pre pre' : List ℤ} {cutTurn cutTurn' : ℤ}
    {entryTurn entryTurn' : ℤ} {suffix suffix' : List ℤ}
    {finalTurn finalTurn' : ℤ}
    (hpair :
      (hexCSCutPrefixOutput pre cutTurn,
          hexCSCutSuffixOutput entryTurn suffix finalTurn) =
        (hexCSCutPrefixOutput pre' cutTurn',
          hexCSCutSuffixOutput entryTurn' suffix' finalTurn')) :
    pre ++ [cutTurn] ++ suffix ++ [finalTurn] =
      pre' ++ [cutTurn'] ++ suffix' ++ [finalTurn'] := by
  have hdecode := congrArg hexCSDecodeCutPair hpair
  simpa using hdecode


theorem hexCSCutPair_length_add_one
    (pre : List ℤ) (cutTurn entryTurn : ℤ)
    (suffix : List ℤ) (finalTurn : ℤ) :
    (hexCSCutPrefixOutput pre cutTurn).length +
        (hexCSCutSuffixOutput entryTurn suffix finalTurn).length =
      (pre ++ [cutTurn] ++ suffix ++ [finalTurn]).length + 1 := by
  simp only [hexCSCutPrefixOutput, hexCSCutSuffixOutput,
    List.length_append, List.length_cons]
  omega


end
end StatMech.Universality
