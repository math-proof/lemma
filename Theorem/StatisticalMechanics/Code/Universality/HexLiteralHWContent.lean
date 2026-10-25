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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hhc_widthList_nodup (s : HexHWContentHalf) :
    (s.1.map HexBridge.width).Nodup :=
  hbw_widthlist_nodup s.1 s.2


theorem hhc_card_widths (s : HexHWContentHalf) :
    (hhc_widths s).card = s.1.length := by
  classical
  unfold hhc_widths hbw_widthFinset
  simpa using List.toFinset_card_of_nodup (hhc_widthList_nodup s)


end StatMech.Universality
