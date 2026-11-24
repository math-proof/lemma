module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open scoped BigOperators

open HexWalk


def hzc_Dn (a : ℂ) (h0 : ℤ) (N : ℕ) : Type := {ts : List ℤ // ts ∈ hzc_truncFinset a h0 N}

end StatMech.Universality
