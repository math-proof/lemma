/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_completedPrefix (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ :=
  let raw := hlhda_prefixAugment ts hleg
  let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
  raw ++ [hlhd_exitTurn
    (hlhda_terminalEdge raw hraw (hlhda_prefixAugment_ne ts hleg))]


noncomputable def hlhda_completedSuffix (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ :=
  hlhda_suffixAugment ts hleg

noncomputable def hlhda_completedPair (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : List ℤ × List ℤ :=
  (hlhda_completedPrefix ts hleg, hlhda_completedSuffix ts hleg)

end
end StatMech.Universality
