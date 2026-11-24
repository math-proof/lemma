module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


noncomputable def hexDropMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) : ℂ :=
  if hcp : cp ≤ ts.length then (hexVerticesAux_drop a h0 ts cp hcp).choose else a


end StatMech.Universality
