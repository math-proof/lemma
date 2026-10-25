/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part7


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSStartIncidence (T L : ℕ) (hT : 0 < T) : HexCSIncidence T L :=
  ⟨hexCSOrigin T L hT, 0⟩

end
end StatMech.Universality
