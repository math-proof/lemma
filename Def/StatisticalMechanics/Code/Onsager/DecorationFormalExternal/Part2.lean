/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalAvoidRoot
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  PowerSeries.subst (ons_decFormalAvoidLog L a b d) (PowerSeries.exp ℂ)

end StatMech.Onsager
