/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
open MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {E F : Type*}


def dualConfigEquiv (edgeDual : E ≃ F) : ConfigSpace E ≃ ConfigSpace F where
  toFun omega f := !(omega (edgeDual.symm f))
  invFun eta e := !(eta (edgeDual e))
  left_inv := by intro omega; funext e; simp
  right_inv := by intro eta; funext f; simp

end PeriodicPlanar
end FK
end StatMech
