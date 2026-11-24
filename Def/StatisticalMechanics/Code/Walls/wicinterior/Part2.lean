module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
public import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

variable {a : Site 2}


def wic_LeftBoundaryConnected (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ u v : Site 2, u ∈ wic_leftBoundary Vc → v ∈ wic_leftBoundary Vc →
    (offSupport Vc).Reachable u v


end Lattice
end StatMech
