/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchDual.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

def npd_P00 (f : Site 2) : Site 2 := ![f 0, f 1]


def npd_P10 (f : Site 2) : Site 2 := ![f 0 + 1, f 1]


def npd_P11 (f : Site 2) : Site 2 := ![f 0 + 1, f 1 + 1]


def npd_P01 (f : Site 2) : Site 2 := ![f 0, f 1 + 1]


end Lattice
end StatMech
