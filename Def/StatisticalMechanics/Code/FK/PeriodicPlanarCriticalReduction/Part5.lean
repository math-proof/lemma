/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part4
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


section Countable

variable [Countable V]


noncomputable def PeriodicGraph.criticalPoint
    (P : PeriodicGraph V) (q : ℝ) : ℝ :=
  sSup (P.subcriticalSet q)

end Countable


def OffCriticalSharpness (percolates : ℝ → Prop) (pc : ℝ) : Prop :=
  (∀ p ∈ Ioo (0 : ℝ) 1, p < pc → ¬percolates p) ∧
  (∀ p ∈ Ioo (0 : ℝ) 1, pc < p → percolates p)


def DualSubcriticalCoverage
    (dualPercolates : ℝ → Prop) (pc q : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1, p < pc →
    dualPercolates (dualParam p q)


def DualNoCoexistence
    (primalPercolates dualPercolates : ℝ → Prop) (q : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1,
    ¬(primalPercolates p ∧ dualPercolates (dualParam p q))


end PeriodicPlanar
end FK
end StatMech
