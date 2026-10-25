/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part4


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSReflectVertex {T L : ℕ} (v : HexCSVertex T L) :
    HexCSVertex T L :=
  ⟨hexAWReflectCoord v.1, (hexCSVertexSet_reflect_iff T L v.1).2 v.2⟩

end
end StatMech.Universality
