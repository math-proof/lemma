/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedBounds
import Theorem.StatisticalMechanics.Code.Onsager.KWMultiaffineBounded
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget.Part2


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

noncomputable def ons_weightedSpinCharacterSum
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) : ℂ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
      ∏ edge ∈ F, weight edge

end StatMech.Onsager
