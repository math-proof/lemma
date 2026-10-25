/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardReversibleCycleCoefficient
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u

open StatMech.Onsager


def KWGraphLoopReversalInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) : Prop :=
  ∀ {n : ℕ} [NeZero n] (loop : Fin n → G.Dart),
    kwGraphLoopNonbacktracking G loop →
      kwGraphLoopScalar G phase (kwGraphLoopRev loop) =
        kwGraphLoopScalar G phase loop

end StatMech.FrontierA
