/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_depth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) : ℤ :=
  hexAWDepth (hlhc_prefixCoord ts hleg.1 k)


noncomputable def hlhd_height (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) : ℝ :=
  hlhd_depth ts hleg k


def HLHDLiteralHalfSpace (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) : Prop :=
  ∀ k, 0 < k → k ≤ ts.length →
    hlhd_height ts hleg 0 < hlhd_height ts hleg k

end
end StatMech.Universality
