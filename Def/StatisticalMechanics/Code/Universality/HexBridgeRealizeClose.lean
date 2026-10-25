/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


noncomputable def hbr_lamCum (f : ℕ → ℝ) (v : ℕ) : ℝ := ∑ w ∈ Finset.range (v + 1), f w


end StatMech.Universality
