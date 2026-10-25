/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

def HexCSNewSideWalk (T : ℕ) (hT : 1 ≤ T) (ts : List ℤ) : Prop :=
  HexCSSideWalkAtWidth (T + 1) (by omega) ts ∧
    ¬ HexCSSideWalkAtWidth T (by omega) ts


end
end StatMech.Universality
