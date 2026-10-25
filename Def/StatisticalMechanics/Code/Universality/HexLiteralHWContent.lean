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


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


def HexHWContentHalf : Type :=
  {bs : List HexBridge // StrictDecreasingWidths bs}


def hhc_halfTurns (s : HexHWContentHalf) : List ℤ :=
  (s.1.map HexBridge.content).flatten


noncomputable def hhc_widths (s : HexHWContentHalf) : Finset ℕ :=
  hbw_widthFinset s.1


end StatMech.Universality
