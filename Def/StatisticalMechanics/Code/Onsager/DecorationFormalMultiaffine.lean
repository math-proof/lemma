/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleBalanced
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalClose
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeClassification


namespace StatMech.Onsager

open BigOperators

def ons_secondDifferenceFactor (k : ℕ) : ℂ :=
  (2 : ℂ) ^ k - 2 + (0 : ℂ) ^ k

noncomputable def ons_decFormalSecondDifference
    {L : ℕ} (series : MvPowerSeries (ons_DecEdge L) ℂ)
    (edge : ons_DecEdge L) : MvPowerSeries (ons_DecEdge L) ℂ :=
  fun m ↦ ons_secondDifferenceFactor (m edge) *
    MvPowerSeries.coeff m series

end StatMech.Onsager
