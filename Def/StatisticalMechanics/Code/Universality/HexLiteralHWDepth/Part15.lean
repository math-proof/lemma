/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part16


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_intervalCoords (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) : List HexAWCoord :=
  List.ofFn (fun r : Fin ((hlhd_intervalRaw ts p).length + 1) =>
    hlhc_prefixCoord ts hleg.1 (p.1 + r.val))

end
end StatMech.Universality
