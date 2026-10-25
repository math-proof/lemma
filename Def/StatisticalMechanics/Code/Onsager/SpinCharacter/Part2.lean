/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_spinCharacterSum (L : ℕ) [Fact (2 < L)]
    (x : ℝ) (a b : Fin 2) : ℝ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card

end StatMech.Onsager
