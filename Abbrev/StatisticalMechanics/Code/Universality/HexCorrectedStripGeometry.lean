/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

abbrev HexCSVertex (T L : ℕ) := {c : HexAWCoord // c ∈ hexCSVertexSet T L}

end
end StatMech.Universality
