/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCS_endpoint_dropLast_isLegalSAW
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hne : ts ≠ [])
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW) :
    (ofTurns a h0 ts.dropLast).IsLegalSAW := by
  induction ts using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton base t ih =>
      simpa using (endpointIsLegalSAW_append_one_iff a h0 base t).mp hlegal |>.1


end
end StatMech.Universality
