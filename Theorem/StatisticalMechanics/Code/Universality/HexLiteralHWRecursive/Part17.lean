/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part17


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


@[simp] theorem hlhr_literalBridge_width (ts : List ℤ) (hleg hhalf) (p) :
    (hlhr_literalBridge ts hleg hhalf p).width = hlhr_latticeWidth ts p.1 := rfl

@[simp] theorem hlhr_literalBridge_content (ts : List ℤ) (hleg hhalf) (p) :
    (hlhr_literalBridge ts hleg hhalf p).content =
      hlhr_intervalContent ts p.1 := rfl


end StatMech.Universality
