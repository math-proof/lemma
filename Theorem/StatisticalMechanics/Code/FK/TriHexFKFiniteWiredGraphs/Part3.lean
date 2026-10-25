/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part3
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteTriangleEdgeChart_bijective (n : Nat) :
    Function.Bijective (triHexPlanarFiniteTriangleEdgeChart n) := by
  constructor
  · intro a b h
    apply triHexPlanarFiniteTriangleEdge_injective n
    exact congrArg Subtype.val h
  · rintro ⟨e, he⟩
    rw [triHexPlanarFiniteTriangleGraph,
      SimpleGraph.edgeSet_fromEdgeSet] at he
    obtain ⟨⟨a, rfl⟩, _⟩ := he
    exact ⟨a, rfl⟩

end
end StatMech.FK.PeriodicPlanar
