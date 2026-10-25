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
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hexW2_lowerHalf (a : ℂ) (h0 : ℤ) (ts : List ℤ) : HexW2Half where
  mid := a
  head := h0
  turns := ts.take (hexW2_cutPos h0 ts)


noncomputable def hexW2_upperHalf (a : ℂ) (h0 : ℤ) (ts : List ℤ) : HexW2Half where
  mid := hexDropMid a h0 ts (hexW2_cutPos h0 ts)
  head := h0 + (ts.take (hexW2_cutPos h0 ts)).sum
  turns := ts.drop (hexW2_cutPos h0 ts)


noncomputable def hexW2_split (a : ℂ) (h0 : ℤ) (memD : List ℤ → Prop) :
    {ts // memD ts} → HexW2Half × HexW2Half :=
  fun d => (hexW2_lowerHalf a h0 d.1, hexW2_upperHalf a h0 d.1)


end StatMech.Universality
