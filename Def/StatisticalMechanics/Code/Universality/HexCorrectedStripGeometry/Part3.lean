/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part3


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSOrigin (T L : ℕ) (hT : 0 < T) : HexCSVertex T L :=
  ⟨hexAWOriginCoord, hexCSOrigin_mem T L hT⟩


end
end StatMech.Universality
