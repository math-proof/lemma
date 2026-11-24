module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

abbrev TriHexPlanarFiniteCell (n : Nat) :=
  {z : Site 2 // z ∈ box 2 n}

end
end StatMech.FK.PeriodicPlanar
