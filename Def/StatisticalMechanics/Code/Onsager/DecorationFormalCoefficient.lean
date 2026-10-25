/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleExponent.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising

noncomputable def ons_decComponentSeries
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {I : Type*} [Fintype I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i)) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ∑ i : I, MvPowerSeries.monomial
    (ons_finsetExponent (p i).edges.toFinset)
    (ons_spinCharacter a b
      (ons_evenHomology L (ons_walkOriginalEdges (p i))) : ℂ)

end StatMech.Onsager
