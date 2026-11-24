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
public import Def.StatisticalMechanics.Code.Walls.jc4_dartnextperm
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


theorem jc4_dartNextPerm (K : Set (Site 2)) (hK : K.Finite) : jc4_DartNextPerm K := by
  refine ⟨jc4_dartNextSub_injective K, fun a => ⟨rfl, ?_, ?_, ?_⟩⟩
  · exact jc4_dartOrbitPeriod_pos K hK a
  · exact jc4_dartOrbitPeriod_iterate K a
  · exact jc4_dartOrbitWalk_isCycle K hK a

end Walls
end StatMech
