/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part3
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


section Countable

variable [Countable V]


def PeriodicGraph.wiredPercolates
    (P : PeriodicGraph V) (p q : ℝ) : Prop :=
  0 < P.wiredPercolationProbability p q


def PeriodicGraph.subcriticalSet
    (P : PeriodicGraph V) (q : ℝ) : Set ℝ :=
  {p | p ∈ Ioo (0 : ℝ) 1 ∧ P.wiredPercolationProbability p q = 0}

end Countable
end PeriodicPlanar
end FK
end StatMech
