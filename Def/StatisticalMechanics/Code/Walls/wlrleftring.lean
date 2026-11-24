module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
public import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
public import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wlrleftring
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

variable {a : Site 2}


def wlr_innerRing (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {w | w ∈ jec_leftRegion Vc ∧ w ∉ Vc.support ∧
    ∃ nb : Site 2, (hypercubicLattice 2).Adj w nb ∧ nb ∈ Vc.support}


end Lattice
end StatMech
