module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Def.StatisticalMechanics.Code.Lattice.TurningNumber.Part5
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem orbitPeriod_ge_four_of_fullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    4 ≤ dartOrbitPeriod K a := by
  have hbound := abs_orbit_totalTurnZ_le K a
  have h4 : (4 : ℤ) ≤ |totalTurnZ K a.1 (dartOrbitPeriod K a)| := by
    rcases h with h | h <;> rw [h] <;> decide
  have : (4 : ℤ) ≤ (dartOrbitPeriod K a : ℤ) := le_trans h4 hbound
  exact_mod_cast this

end Lattice
end StatMech
