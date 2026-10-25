/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


noncomputable def hzc_truncFinset (a : ℂ) (h0 : ℤ) (N : ℕ) : Finset (List ℤ) :=
  (hzc_truncSet_finite a h0 N).toFinset


end StatMech.Universality
