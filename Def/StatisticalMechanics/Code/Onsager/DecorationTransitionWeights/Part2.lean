/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


noncomputable def ons_decoratedFullWeightedSpinSum
    (L : ℕ) [Fact (2 < L)]
    (decWeight : Sym2 (ons_Dart L) → ℂ) (a b : Fin 2) : ℂ :=
  ∑ D : ons_DecoratedEvenSubgraph L,
    (ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) *
      ∏ edge ∈ D.1, decWeight edge

end StatMech.Onsager
