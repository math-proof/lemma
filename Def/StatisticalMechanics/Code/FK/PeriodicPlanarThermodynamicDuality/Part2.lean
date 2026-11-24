module
public import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality
open MeasureTheory Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {E F : Type*}


def dualConfigHomeomorph (edgeDual : E ≃ F) : ConfigSpace E ≃ₜ ConfigSpace F where
  toEquiv := dualConfigEquiv edgeDual
  continuous_toFun := continuous_dualConfigEquiv edgeDual
  continuous_invFun := continuous_dualConfigEquiv_symm edgeDual


end PeriodicPlanar
end FK
end StatMech
