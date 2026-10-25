/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Def.StatisticalMechanics.Code.Universality.HexZDivTauClose


namespace StatMech.Universality

open Filter Topology Complex HexWalk

open scoped Topology BigOperators


theorem hzd_witnessEτ_wtContour (h : ℕ) :
    hzd_witnessEτ.wtContour h = hexChiE := hzd_trivial_wt


end StatMech.Universality
