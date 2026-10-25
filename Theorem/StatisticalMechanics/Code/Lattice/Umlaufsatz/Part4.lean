/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Def.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem dominoFaceLoop_isCycle : dominoFaceLoop.IsCycle :=
  orbitFaceWalk_isCycle domino dmD0 dmD0_boundary 6 (by norm_num)
    iterate_dmD_6 domino_orbitFace_injOn


end Lattice
end StatMech
