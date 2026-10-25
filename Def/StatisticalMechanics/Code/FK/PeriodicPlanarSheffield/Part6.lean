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
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def PeriodicPlaneEmbedding.rectGraph
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    SimpleGraph (E.RectVertex a b c d) :=
  P.graph.induce (E.rectVertices a b c d)


def PeriodicPlaneEmbedding.openRectHom
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (eta : ConfigSpace (Sym2 (E.RectVertex a b c d))) :
    FK.openSub (E.rectGraph a b c d) eta →g P.graph where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    rw [FK.openSub_adj] at hxy
    exact SimpleGraph.induce_adj.mp hxy.1

end StatMech.FK.PeriodicPlanar
