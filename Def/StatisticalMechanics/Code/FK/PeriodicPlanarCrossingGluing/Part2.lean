/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing
open Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.openRectToOpenSubgraphHom
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (omega : ConfigSpace (Sym2 V)) :
    FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega) →g
      P.openSubgraph omega where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    rw [FK.openSub_adj] at hxy
    change P.graph.Adj x.1 y.1 ∧ omega s(x.1, y.1) = true
    exact ⟨SimpleGraph.induce_adj.mp hxy.1, hxy.2⟩

end StatMech.FK.PeriodicPlanar
