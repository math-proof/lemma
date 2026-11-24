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
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
public import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def bpc_NotProbed (c : Site 2) (e : Dart) : Prop :=
  e.head + (-rot90Fun e.dir) ≠ c ∧ e.tail + (-rot90Fun e.dir) ≠ c


end Lattice
end StatMech
