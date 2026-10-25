/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


def kwGraphLoopOrientation
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    Fin n ⊕ Fin n → (Fin n → G.Dart)
  | Sum.inl k => ons_rotate k loop
  | Sum.inr k => ons_rotate k (kwGraphLoopRev loop)

end StatMech.FrontierA
