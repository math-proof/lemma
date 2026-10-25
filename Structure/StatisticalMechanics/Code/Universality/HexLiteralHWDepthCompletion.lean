/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HLHDAEndpointColumnWalk (T : ℕ) (ts : List ℤ) where
  legal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW
  horizontal : ∀ k, k < ts.length →
    0 ≤ hexAWBookRe2 (hlhc_prefixCoord ts legal.1 k) ∧
      hexAWBookRe2 (hlhc_prefixCoord ts legal.1 k) ≤ 3 * T
  topCoord : HexAWCoord
  top_white : topCoord.color = .white
  top_depth : hexAWDepth topCoord = T
  endsAt : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid topCoord 0)

end
end StatMech.Universality
