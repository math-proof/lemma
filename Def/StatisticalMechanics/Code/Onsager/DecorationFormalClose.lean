/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSquarefree
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalAssembly
import Theorem.StatisticalMechanics.Code.Onsager.FinalAssembly


namespace StatMech.Onsager

def ons_DecFormalRepeatedEdgeVanishes : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ)
      (edge : ons_DecEdge L), 2 ≤ m edge →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0

end StatMech.Onsager
