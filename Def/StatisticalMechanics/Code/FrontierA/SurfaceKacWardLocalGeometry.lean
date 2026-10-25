/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Structure.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

noncomputable def AdmissibleClosedFlatSurfaceEmbedding.toFlatSpinorEmbedding
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : AdmissibleClosedFlatSurfaceEmbedding g G) :
    SurfaceFlatSpinorEmbedding g G where
  phase := embedding.geometry.phase
  edgeClass := embedding.geometry.edgeClass
  localIntersection := fun edge other =>
    surfaceIntersection (embedding.geometry.edgeClass edge)
      (embedding.geometry.edgeClass other)
  degree_le_three := embedding.geometry.degree_le_three
  phase_reverse := embedding.geometry.phase_reverse
  path_phase_sq := embedding.geometry.path_phase_sq
  closed_phase_sq := embedding.geometry.closed_phase_sq
  simple_cycle_spin_holonomy := embedding.developed_simple_cycle_holonomy
  intersection_formula := embedding.geometry.intersection_formula
  localIntersection_zero := embedding.geometry.disjoint_edge_intersection


end StatMech.FrontierA
