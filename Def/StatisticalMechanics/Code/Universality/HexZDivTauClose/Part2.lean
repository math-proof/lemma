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
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part3


namespace StatMech.Universality

open Filter Topology Complex HexWalk

open scoped Topology BigOperators


noncomputable def hzd_witnessSideContour : HexSideContour ℕ (fun _ => (1 : ℝ)) where
  Eτ := hzd_witnessEτ
  posWit := fun _ => ⟨0, by rw [hzd_witnessEτ_wtContour]; exact hexChiE_pos⟩
  shift := fun h n => h + n
  shift_inj := fun h => add_right_injective h
  shift_wt := fun h n => by
    rw [hzd_witnessEτ_wtContour, hzd_witnessEτ_wtContour]


end StatMech.Universality
