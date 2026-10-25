/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_intervals (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    List (ℕ × ℕ) :=
  hlhr_intervalsAux (hlhd_height ts hleg) ts.length ts.length true 0


def hlhd_intervalTurns (ts : List ℤ) (ps : List (ℕ × ℕ)) : List ℤ :=
  hlhr_intervalTurns ts ps

end
end StatMech.Universality
