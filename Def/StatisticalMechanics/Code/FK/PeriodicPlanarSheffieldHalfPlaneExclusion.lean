/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

def HasOpenComplementaryDualTransverseWalkAt
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) (a b c d : Real) : Prop :=
  ∃ yl yr : W, ∃ dual : Pdual.graph.Walk yl yr,
    ¬dual.Nil ∧
      (∀ {x y : W}, s(x, y) ∈ dual.edges →
        dualConfigEquiv D.edgeDual omega s(x, y) = true) ∧
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex yl) 0 < a ∧
      b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex yr) 0 ∧
      ∀ t : unitInterval,
        c < D.primalEmbedding.coordinates
            (D.dualEmbedding.walkArc dual t) 1 ∧
          D.primalEmbedding.coordinates
            (D.dualEmbedding.walkArc dual t) 1 < d


def HasOpenComplementaryDualTransverseWalks
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∀ a b c d : Real, a < b → c < d →
    D.HasOpenComplementaryDualTransverseWalkAt omega a b c d


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
