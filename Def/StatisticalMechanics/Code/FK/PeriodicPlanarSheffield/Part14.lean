/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part13
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicGraph.openSubgraphTranslateHom
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    SimpleGraph.Hom (P.openSubgraph omega)
      (P.openSubgraph (P.configTranslate z omega)) where
  toFun := P.shift z
  map_rel' := by
    intro x y hxy
    rw [P.openSubgraph_adj] at hxy ⊢
    refine ⟨(P.shift_adj z x y).2 hxy.1, ?_⟩
    simpa [PeriodicGraph.configTranslate] using hxy.2

end StatMech.FK.PeriodicPlanar
