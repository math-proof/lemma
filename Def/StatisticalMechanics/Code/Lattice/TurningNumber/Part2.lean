/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def turn (K : Set (Site 2)) (e : Dart) : ZMod 4 := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then 1
    else if e.tail + (-rot90Fun e.dir) ∈ K then 0
    else 3


noncomputable def turnZ (K : Set (Site 2)) (e : Dart) : ℤ := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then 1
    else if e.tail + (-rot90Fun e.dir) ∈ K then 0
    else -1


end Lattice
end StatMech
