module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Instance.StatisticalMechanics.Code.Universality.HexZConvClose


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


noncomputable def hzc_wtγ (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) (d : hzc_Dn a h0 N) : ℝ :=
  hexSAWwt a h0 x d.1


end StatMech.Universality
