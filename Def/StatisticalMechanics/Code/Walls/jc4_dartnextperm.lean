module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.StarHullPeriod
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc4_dartnextperm
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_dartnextperm.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc4_DartNextPerm (K : Set (Site 2)) : Prop :=
  Function.Injective (dartNextSub K) ∧
    ∀ a : {e : Dart // IsBoundaryDart K e},
      dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a ∧
      0 < dartOrbitPeriod K a ∧
      (dartNextSub K)^[dartOrbitPeriod K a] a = a ∧
      (dartOrbitWalk K a).IsCycle


end Walls
end StatMech
