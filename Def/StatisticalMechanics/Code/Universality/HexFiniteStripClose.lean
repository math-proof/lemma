module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


noncomputable def hfs_stMid (m : ℂ) (h : ℤ) : List ℤ → ℂ
  | [] => m
  | t :: ts => hfs_stMid (m + halfStep h + halfStep (h + t)) (h + t) ts


def hfs_stHead (h : ℤ) : List ℤ → ℤ
  | [] => h
  | t :: ts => hfs_stHead (h + t) ts


end StatMech.Universality
