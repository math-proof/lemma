/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Instance.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexAWIncidenceEquiv (T L : ℕ) :
    (HexAWVertex T L × Fin 3) ≃ HexAWIncidence T L where
  toFun p := ⟨p.1, p.2⟩
  invFun e := (e.vtx, e.edge)
  left_inv _ := rfl
  right_inv _ := rfl

end
end StatMech.Universality
