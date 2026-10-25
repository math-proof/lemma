/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part5


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexAWRightFixedIndex (n L : ℕ) (hn : 0 < n) :
    HexAWFixedIndex (2 * n) L (by omega) :=
  ⟨hexAWRightFixedIncidence n L hn,
    hexAWRightFixedIncidence_mem_boundary n L hn,
    hexAWRightFixedIncidence_reflect n L hn,
    by
      intro h
      have hv := congrArg (fun e => e.vtx.1.color) h
      simp [hexAWRightFixedIncidence, hexAWRightFixedCoord,
        hexAWStartIncidence, hexAWOrigin, hexAWOriginCoord] at hv⟩


end
end StatMech.Universality
