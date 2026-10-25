/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeFull.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


def hexWall3_ReachesWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re


def hexWall3_mem (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ b : HexBridge, b.width = T ∧ b.content = ts
    ∧ hexWall3_ReachesWidth a h0 T ts ∧ (HexWalk.ofTurns a h0 ts).IsLegalSAW


end StatMech.Universality
