/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part2
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def PeriodicGraph.cluster (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (v : V) : Set V :=
  {w | (P.openSubgraph omega).Reachable v w}


def PeriodicGraph.HasInfiniteCluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∃ x, (P.cluster omega x).Infinite


def PeriodicGraph.percolationEvent (P : PeriodicGraph V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.cluster omega P.root).Infinite}

section Countable

variable [Countable V]


noncomputable def PeriodicGraph.wiredPercolationProbability
    (P : PeriodicGraph V) (p q : ℝ) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real P.percolationEvent
  else 0

end Countable
end PeriodicPlanar
end FK
end StatMech
