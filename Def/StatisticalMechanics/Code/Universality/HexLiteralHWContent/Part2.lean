/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


def hhc_plusBridge : HexBridge where
  width := 1
  width_pos := one_pos
  content := [1]
  content_ne := by simp

def hhc_minusBridge : HexBridge where
  width := 1
  width_pos := one_pos
  content := [-1]
  content_ne := by simp

def hhc_plusHalf : HexHWContentHalf :=
  ⟨[hhc_plusBridge], by simp [StrictDecreasingWidths]⟩

def hhc_minusHalf : HexHWContentHalf :=
  ⟨[hhc_minusBridge], by simp [StrictDecreasingWidths]⟩

end StatMech.Universality
