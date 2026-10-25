/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def dmD0 : Dart := mkDart ![0, 0] ![0, -1] unitWt_my

noncomputable def dmD1 : Dart := mkDart ![0, 0] ![-1, 0] unitWt_mx

noncomputable def dmD2 : Dart := mkDart ![0, 0] ![0, 1] unitWt_py

noncomputable def dmD3 : Dart := mkDart ![1, 0] ![0, 1] unitWt_py

noncomputable def dmD4 : Dart := mkDart ![1, 0] ![1, 0] unitWt_px

noncomputable def dmD5 : Dart := mkDart ![1, 0] ![0, -1] unitWt_my


end Lattice
end StatMech
