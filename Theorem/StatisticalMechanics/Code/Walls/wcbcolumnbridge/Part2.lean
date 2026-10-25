/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Def.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wcb_dartColumn_eq_head (z : Site 2) (d : (hypercubicLattice 2).Dart)
    (h : jec_rayEdge z s(d.toProd.1, d.toProd.2)) :
    wcb_dartColumn d = d.toProd.2 0 :=
  wcb_rayEdge_column z d.toProd.1 d.toProd.2 h


theorem wcb_dart_edge (d : (hypercubicLattice 2).Dart) :
    d.edge = s(d.toProd.1, d.toProd.2) := SimpleGraph.Dart.edge_mk ..


theorem wcb_crossing_edges_distinct_columns (z : Site 2)
    (d₁ d₂ : (hypercubicLattice 2).Dart)
    (h₁ : jec_rayEdge z d₁.edge) (h₂ : jec_rayEdge z d₂.edge)
    (hcol : wcb_dartColumn d₁ = wcb_dartColumn d₂) :
    d₁.edge = d₂.edge := by
  rw [wcb_dart_edge] at h₁ h₂ ⊢
  exact wcb_rayEdge_injOn_column z d₁.toProd.1 d₁.toProd.2 d₂.toProd.1 d₂.toProd.2 h₁ h₂ hcol


end Lattice
end StatMech
