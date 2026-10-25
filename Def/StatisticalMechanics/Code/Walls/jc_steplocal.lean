/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
open SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc_travel (e : Dart) : Site 2 := -rot90Fun e.dir


def jc_headTravel (e : Dart) : Site 2 := e.head + jc_travel e


def jc_tailTravel (e : Dart) : Site 2 := e.tail + jc_travel e

end Walls
end StatMech
