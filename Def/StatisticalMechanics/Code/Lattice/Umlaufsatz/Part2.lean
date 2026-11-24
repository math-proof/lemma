module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part2
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def unitCellFaceLoop :
    (faceBoundaryGraph unitCell).Walk (dartFace ucDart0) (dartFace ucDart0) :=
  (dartOrbitFaceWalk unitCell ucDart0 ucDart0_boundary 4).copy rfl (by rw [iterate_ucDart_4])


end Lattice
end StatMech
