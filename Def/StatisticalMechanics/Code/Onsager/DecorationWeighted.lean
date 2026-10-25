/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedAffine.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_decoratedWeightedSpinWeight
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) : ℂ :=
  (ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) *
    ∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge

end StatMech.Onsager
