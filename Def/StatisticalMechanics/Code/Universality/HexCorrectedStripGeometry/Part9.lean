/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part8


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSCanonicalHeading {T L : ℕ} (e : HexCSIncidence T L) : ℤ :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => if 0 ≤ hexAWTrans e.vtx.1 then 4 else -2
  | .white, 0 => 1
  | .white, 1 => 3
  | .white, 2 => -1
  | _, _ => hexAWHeading e.vtx.1 e.edge


end
end StatMech.Universality
