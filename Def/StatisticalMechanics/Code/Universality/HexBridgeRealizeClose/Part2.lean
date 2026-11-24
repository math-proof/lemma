module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


noncomputable def hbr_witnessEmb : HexColumnEmb Unit Unit where
  wtSAW := fun _ => (1 : ℝ)
  emb := fun _ => ()
  emb_inj := fun a b _ => Subsingleton.elim a b
  wtSAW_nn := fun _ => zero_le_one
  scale := fun _ => 1


end StatMech.Universality
