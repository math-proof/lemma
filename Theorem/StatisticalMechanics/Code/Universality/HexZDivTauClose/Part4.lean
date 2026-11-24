module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
public import Def.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Filter Topology Complex HexWalk

open scoped Topology BigOperators


theorem hzd_sideContour_fires :
    ¬ Summable hzd_witnessEτ.wtContour :=
  hzd_tau_side_diverges hzd_witnessSideContour ⟨1, le_rfl, one_pos⟩

end StatMech.Universality
