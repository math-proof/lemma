/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripStartReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexCSOutsideStartCoord : HexAWCoord := ⟨0, 0, .white⟩

end
end StatMech.Universality
