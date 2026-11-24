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
public import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
public import Def.StatisticalMechanics.Code.Lattice.GaussBonnet
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem gbCurvature_mem (K : Set (Site 2)) (e : Dart) :
    gbCurvature K e = 1 ∨ gbCurvature K e = 0 ∨ gbCurvature K e = -1 :=
  turnZ_mem K e


theorem curvature_sum_eq_totalTurnZ (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = ∑ i ∈ Finset.range p, gbCurvature K ((dartNext K)^[i] e) := rfl


end Lattice
end StatMech
