/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part13


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalFirstReturnTrunc
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (N : ℕ) : MvPowerSeries (ons_DecEdge L) ℂ :=
  ∑ atom : ons_DecFirstReturnAtomBounded L d N,
    MvPowerSeries.monomial (ons_decBoundedAtomExponent atom)
      (ons_decBoundedAtomWeight L a b atom)

end StatMech.Onsager
