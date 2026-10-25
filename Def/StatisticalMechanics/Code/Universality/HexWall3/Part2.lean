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
import Theorem.StatisticalMechanics.Code.Universality.HexWall3


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


noncomputable def hexWall3_column (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (hsummable : Summable (fun w : {ts // hexWall3_mem a h0 T ts} =>
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices))
    (hle_one : (∑' w : {ts // hexWall3_mem a h0 T ts},
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices) ≤ 1) :
    HexColumn T χ :=
  hexColumnOfWidth a h0 T χ (hexWall3_mem a h0 T)
    (hexWall3_mem_reaches a h0 T) hsummable hle_one


end StatMech.Universality
