module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part2
open scoped BigOperators
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager


def kwGraphLoopNonbacktracking
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : Prop :=
  ∀ k, (loop k).snd = (loop (k + 1)).fst ∧
    (loop k).edge ≠ (loop (k + 1)).edge


noncomputable def kwGraphLoopAdjacency
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : ℂ :=
  ∏ k, if (loop k).snd = (loop (k + 1)).fst ∧
      (loop k).edge ≠ (loop (k + 1)).edge then 1 else 0

end StatMech.FrontierA
