/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Exact3D.Ising3D.Part2
open MeasureTheory


namespace StatMech

namespace Exact3D

open StatMech.Lattice


@[simp] theorem twoPointOnXAxis_zero (β : ℝ) :
    twoPointOnXAxis β 0 = 1 := by
  simp [twoPointOnXAxis, twoPointAtDisplacement, ising3DPlusTwoPoint, Ising.spin_sq]

@[simp] theorem freeTwoPointOnXAxis_zero (β : ℝ) :
    freeTwoPointOnXAxis β 0 = 1 := by
  simp [freeTwoPointOnXAxis, freeTwoPointAtDisplacement, ising3DFreeTwoPoint, Ising.spin_sq]


end Exact3D
end StatMech
