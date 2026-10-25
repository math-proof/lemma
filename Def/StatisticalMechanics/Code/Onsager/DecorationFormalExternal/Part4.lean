/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Instance.StatisticalMechanics.Code.Onsager.DecorationFormalExternal


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalFirstReturnCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
    ∑ loop : Fin (r + 1) → ons_Dart L,
      if ons_decIsFirstReturnLoop d loop ∧
          ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0

noncomputable def ons_decFormalFirstReturn
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalFirstReturnCoeff L a b d

end StatMech.Onsager
