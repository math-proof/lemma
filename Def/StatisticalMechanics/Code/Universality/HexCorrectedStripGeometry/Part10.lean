/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part9


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

noncomputable def hexCSCanonicalWinding {T L : ℕ}
    (e : HexCSIncidence T L) : ℝ :=
  (Real.pi / 3) * ((hexCSCanonicalHeading e : ℝ) - 1)


def hexCSBoundaryClass {T L : ℕ} (e : HexCSIncidence T L) :
    HexPairedBoundaryClass :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => .side
  | .white, 0 => .top
  | .white, 1 => .slant
  | .white, 2 => .slant
  | _, _ => .top


end
end StatMech.Universality
