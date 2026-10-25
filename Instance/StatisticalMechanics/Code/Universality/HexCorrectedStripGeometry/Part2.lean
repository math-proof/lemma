/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part5


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

instance hexCSIsInterior_decidable {T L : ℕ} (e : HexCSIncidence T L) :
    Decidable (hexCSIsInterior e) := by
  unfold hexCSIsInterior
  infer_instance

end
end StatMech.Universality
