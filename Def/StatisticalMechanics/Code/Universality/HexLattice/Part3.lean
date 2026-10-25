/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part2


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

noncomputable def halfStep (h : ℤ) : ℂ := (1 / 2 : ℂ) * hexUnit h


noncomputable def midsAux (m : ℂ) (h : ℤ) : List ℤ → List ℂ
  | [] => [m]
  | t :: ts => m :: midsAux (m + halfStep h + halfStep (h + t)) (h + t) ts


noncomputable def mids (w : HexWalk) : List ℂ := midsAux w.startMid w.h0 w.turns

end HexWalk
end StatMech.Universality
