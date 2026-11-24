module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
public import Theorem.StatisticalMechanics.Code.Walls.jc6_singlecycle.Part2
public import Def.StatisticalMechanics.Code.Walls.jc7loopseparates
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7loopseparates.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc7_loopSeparates (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : jc7_LoopSeparates K hK e he :=
  ⟨fun hadj hu hv => jc7_loop_localConstancy K hK e he hadj hu hv,
   fun hadj hbd => jc7_loop_leftRegion_bdEdge_support K hK e he hadj hbd⟩


end Walls
end StatMech
