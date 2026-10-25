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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part8


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


@[simp] theorem hhc_bridgeOfNonempty_width (ts : List ℤ) (hne : ts ≠ []) :
    (hhc_bridgeOfNonempty ts hne).width = ts.length := rfl

@[simp] theorem hhc_bridgeOfNonempty_content (ts : List ℤ) (hne : ts ≠ []) :
    (hhc_bridgeOfNonempty ts hne).content = ts := rfl


end StatMech.Universality
