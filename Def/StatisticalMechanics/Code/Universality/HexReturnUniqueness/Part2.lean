/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness


namespace StatMech.Universality

open Complex HexWalk


namespace HexReturnCoord

def IsUnit (d : HexReturnCoord) : Prop :=
  d = ⟨1, 0⟩ ∨ d = ⟨1, 1⟩ ∨ d = ⟨0, 1⟩ ∨
    d = ⟨-1, 0⟩ ∨ d = ⟨-1, -1⟩ ∨ d = ⟨0, -1⟩

end HexReturnCoord
end StatMech.Universality
