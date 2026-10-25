/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part2
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def SubcriticalTwoPointExponentialDecay
    [Countable V] (P : PeriodicGraph V) (q pc : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) pc, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x y : V,
      P.wiredTwoPointProbability p q x y ≤
        C * Real.exp (-c * (P.graph.dist x y : ℝ))


def CriticalSurfacePhaseBoundary (surface : ℝ → ℝ) (pc : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1,
    (surface p < 0 ↔ p < pc) ∧ (0 < surface p ↔ pc < p)


end PeriodicPlanar
end FK
end StatMech
