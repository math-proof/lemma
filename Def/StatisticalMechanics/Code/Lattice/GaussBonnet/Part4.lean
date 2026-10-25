/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

def EulerCharOne (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  revCount K a = (contourEulerChar (dartOrbitPeriod K a) : ℤ) ∨
    revCount K a = -(contourEulerChar (dartOrbitPeriod K a) : ℤ)


end Lattice
end StatMech
