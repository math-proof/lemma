module
public import Theorem.StatisticalMechanics.Code.Walls.kc10core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
public import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
public import Theorem.StatisticalMechanics.Code.Walls.kc12core.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


def kc12_component (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) : Set (Site 2) :=
  {y | (offSupport Vc).Reachable z y}


end Walls
end StatMech
