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
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_decoratedSpinWeight
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2)
    (D : ons_DecoratedEvenSubgraph L) : ℝ :=
  let F := ons_originalEdgesOfDecorated L D
  ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card

end StatMech.Onsager
