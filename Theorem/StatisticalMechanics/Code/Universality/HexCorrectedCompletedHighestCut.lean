/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8
import Def.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSCompletedSplit_injective
    (T : ℕ) (hT : 1 ≤ T) :
    Function.Injective (hexCSCompletedSplit T hT) := by
  intro d e hde
  let Gd := hexCSNewSideDepthData T hT d
  let Ge := hexCSNewSideDepthData T hT e
  apply Subtype.ext
  apply hlhda_completedPair_injective Gd.legal Ge.legal
  apply Prod.ext
  · have h := congrArg (fun p => p.1.1) hde
    simpa [hexCSCompletedSplit, hlhda_completedPair, Gd, Ge] using h
  · have h := congrArg (fun p => p.2.1) hde
    simpa [hexCSCompletedSplit, hlhda_completedPair, Gd, Ge] using h

theorem hexCSCompletedSplit_length
    (T : ℕ) (hT : 1 ≤ T)
    (d : {ts : List ℤ // HexCSNewSideWalk T hT ts}) :
    (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).1.1).endpointNumVertices +
        (ofTurns hexAWStart 1
          (hexCSCompletedSplit T hT d).2.1).endpointNumVertices =
      (ofTurns hexAWStart 1 d.1).endpointNumVertices + 5 := by
  let G := hexCSNewSideDepthData T hT d
  have hlen := hlhda_completedPair_length d.1 G.legal
  simpa [hexCSCompletedSplit, hlhda_completedPair,
    HexWalk.endpointNumVertices, G] using hlen

end
end StatMech.Universality
