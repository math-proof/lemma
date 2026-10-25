/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part9
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


omit [DecidableRel G.Adj] in


theorem wiredSub_componentMk_eq_of_bdry {ω : ConfigSpace (Sym2 V)} {x y : V}
    (hx : bdry x) (hy : bdry y) :
    (wiredSub G bdry ω).connectedComponentMk x
      = (wiredSub G bdry ω).connectedComponentMk y := by
  by_cases h : x = y
  · rw [h]
  · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [wiredSub, SimpleGraph.sup_adj]; right
    rw [boundaryCliqueGraph_adj]; exact ⟨h, hx, hy⟩


end IsingFK
end StatMech
