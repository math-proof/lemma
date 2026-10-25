/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part3
import Theorem.StatisticalMechanics.Code.Walls.wlrleftring.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


def wlr_ConsecutiveInnerStep (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ s s' w w' : Site 2, s ∈ Vc.support → s' ∈ Vc.support →
    (hypercubicLattice 2).Adj s s' →
    w ∈ wlr_innerRing Vc → (hypercubicLattice 2).Adj w s →
    w' ∈ wlr_innerRing Vc → (hypercubicLattice 2).Adj w' s' →
    (offSupport Vc).Reachable w w'

end Lattice
end StatMech
