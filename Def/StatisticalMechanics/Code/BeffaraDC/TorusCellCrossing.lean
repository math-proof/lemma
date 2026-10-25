/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Abbrev.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusHorizontalEdge (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    TorusAmbientEdge L :=
  ⟨s((x, y), (x + 1, y)), by
    simp only [SimpleGraph.mem_edgeFinset, onsTorusGraph]
    exact Or.inr ⟨rfl, Or.inr (by ring)⟩⟩


def torusVerticalEdge (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    TorusAmbientEdge L :=
  ⟨s((x, y), (x, y + 1)), by
    simp only [SimpleGraph.mem_edgeFinset, onsTorusGraph]
    exact Or.inl ⟨rfl, Or.inr (by ring)⟩⟩

end StatMech.BeffaraDC
