/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedTarget.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedAffine


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

noncomputable def ons_weightedSpinEdgeCoefficient
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (edge : Sym2 (ZMod L × ZMod L)) : ℂ :=
  ∑ F ∈ (evenSubgraphs (onsTorusGraph L)).filter (edge ∈ ·),
    (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
      ∏ f ∈ F, weight f

end StatMech.Onsager
