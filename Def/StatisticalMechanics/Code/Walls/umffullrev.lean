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
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanOrbitCycle.Part2
open scoped BigOperators
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def umf_WindsAtMostOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4


def umf_WindsAtLeastOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0


end Lattice
end StatMech
