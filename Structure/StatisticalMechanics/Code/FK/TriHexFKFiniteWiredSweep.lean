/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

structure TriHexFiniteWiredLevel where
  Cell : Type
  Vertex : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  terminal : Cell → Fin 3 → Vertex
  boundary : Vertex → Prop
  boundaryDecidable : DecidablePred boundary
  root : Vertex


end
end StatMech.FK.PeriodicPlanar
