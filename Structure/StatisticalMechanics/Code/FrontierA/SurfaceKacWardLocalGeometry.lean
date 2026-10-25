/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

structure SurfaceLocalSpinorGeometry (g : Nat)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  cellular : FiniteCellularGraphEmbedding G
  genus_eq : cellular.genus = g
  phase : G.Dart -> G.Dart -> Complex
  direction : G.Dart -> Complex
  edgeClass : Sym2 V -> SurfaceHomology g
  degree_le_three : forall vertex, G.degree vertex <= 3
  direction_ne_zero : forall dart, direction dart ≠ 0
  direction_reverse : forall dart,
    direction dart.symm = -direction dart
  phase_sq_transport : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      phase dart next ^ 2 * direction dart = direction next
  phase_reverse : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      phase next.symm dart.symm = (phase dart next)⁻¹
  disjoint_edge_intersection : forall edge other : Sym2 V,
    Disjoint edge.toFinset other.toFinset ->
      surfaceIntersection (edgeClass edge) (edgeClass other) = 0


end StatMech.FrontierA
