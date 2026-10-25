/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexW2Weight


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hexW2_halfWt_nonneg (x : ℝ) (hx : 0 ≤ x) (b : HexW2Half) :
    0 ≤ hexW2_halfWt x b :=
  hexSAWwt_nonneg b.mid b.head hx b.turns


end StatMech.Universality
