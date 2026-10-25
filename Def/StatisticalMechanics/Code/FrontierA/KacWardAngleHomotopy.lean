/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
import Mathlib.Topology.Connected.TotallyDisconnected
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy
open scoped BigOperators
open Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwLoopPhaseProduct
    {D : Type*} {n : ℕ} [NeZero n]
    (phase : D → D → ℂ) (loop : Fin n → D) : ℂ :=
  ∏ k, phase (loop k) (loop (k + 1))


end StatMech.FrontierA
