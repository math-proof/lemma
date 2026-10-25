/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part2
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteStarEdge_mem (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    triHexPlanarFiniteStarEdge n a ∈
      (triHexPlanarFiniteStarGraph n).edgeSet := by
  rw [triHexPlanarFiniteStarGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨⟨a, rfl⟩, ?_⟩
  rw [Sym2.mem_diagSet]
  change ¬s(Sum.inl a.1,
    Sum.inr (triHexPlanarFiniteTerminalMap n a.1 a.2)).IsDiag
  rw [Sym2.mk_isDiag_iff]
  exact Sum.inl_ne_inr

end
end StatMech.FK.PeriodicPlanar
