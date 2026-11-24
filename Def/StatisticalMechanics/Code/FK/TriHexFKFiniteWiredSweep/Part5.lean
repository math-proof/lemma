module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part2
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

noncomputable def triHexPlanarFiniteRootCell (n : Nat) :
    TriHexPlanarFiniteCell n :=
  ⟨0, by simp⟩


noncomputable def triHexPlanarFiniteWiredLevel (n : Nat) :
    TriHexFiniteWiredLevel where
  Cell := TriHexPlanarFiniteCell n
  Vertex := TriHexPlanarFiniteTerminal n
  cellFintype := inferInstance
  cellDecidableEq := inferInstance
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  terminal := triHexPlanarFiniteTerminalMap n
  boundary := triHexPlanarFiniteBoundary n
  boundaryDecidable := inferInstance
  root := triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0


end
end StatMech.FK.PeriodicPlanar
