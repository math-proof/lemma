/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part7


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexAWFixedIndex_subsingleton_even (n L : ℕ) (hn : 0 < n) :
    ∀ k : HexAWFixedIndex (2 * n) L (by omega),
      k = hexAWRightFixedIndex n L hn := by
  intro k
  obtain ⟨m, hm, hwidth, hcoord, hedge⟩ := hexAWFixedIndex_eq_right k
  have hmn : m = n := by omega
  subst m
  apply Subtype.ext
  rw [HexIncidence.mk.injEq]
  exact ⟨Subtype.ext hcoord, hedge⟩

end
end StatMech.Universality
