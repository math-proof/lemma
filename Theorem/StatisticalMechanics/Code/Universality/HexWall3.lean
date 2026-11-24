module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeFull.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
public import Def.StatisticalMechanics.Code.Universality.HexWall3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


theorem hexWall3_mem_reaches (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (h : hexWall3_mem a h0 T ts) :
    ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re := by
  obtain ⟨b, _, _, hreach, _⟩ := h
  exact hreach


end StatMech.Universality
