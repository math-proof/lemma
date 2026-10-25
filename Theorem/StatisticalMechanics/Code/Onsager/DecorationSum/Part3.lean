/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Def.StatisticalMechanics.Code.Onsager.DecorationSum.Part3


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_decoratedSpinWeight_eq_external
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) :
    ons_decoratedSpinWeight L x a b D =
      ons_spinCharacter a b
          (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) *
        x ^ (ons_decoratedExternalEdges D.1).card := by
  change ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) *
        x ^ (ons_originalEdgesOfDecorated L D).card = _
  rw [ons_originalEdgesOfDecorated_card]

end StatMech.Onsager
