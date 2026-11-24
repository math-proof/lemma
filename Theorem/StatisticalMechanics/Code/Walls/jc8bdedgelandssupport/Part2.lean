module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
public import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
public import Def.StatisticalMechanics.Code.Walls.jc8bdedgelandssupport
open SimpleGraph Function Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8bdedgelandssupport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8_bdEdgeLandsSupport (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : jc8_BdEdgeLandsSupport K hK e he :=
  fun hadj hbd => jc8_bdEdge_lands_support K hK e he hadj hbd


end Walls
end StatMech
