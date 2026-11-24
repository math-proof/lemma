module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open List

open scoped BigOperators


theorem hbw_widthlist_nodup (bs : List HexBridge) (h : StrictDecreasingWidths bs) :
    (bs.map HexBridge.width).Nodup := by
  have hp : (bs.map HexBridge.width).Pairwise (· ≠ ·) := by
    rw [List.pairwise_map]
    exact h.imp (fun hab => ne_of_gt hab)
  exact hp


end StatMech.Universality
