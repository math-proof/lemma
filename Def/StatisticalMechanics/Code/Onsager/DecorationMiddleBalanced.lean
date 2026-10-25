/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness.Part3


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_decMiddleBalanced
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega t lambda : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L ⊕ Fin 2) (ons_Dart L ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    (ons_KWmatDecorationWeightedPhase L
      (ons_scaleDecEdgeWeight decWeight
        (ons_decChainEdge site 1) 0) omega 1 1)
    ((t * lambda) • ons_decMiddleU L decWeight omega site)
    (lambda⁻¹ • ons_decMiddleV L decWeight omega 1 1 site)
    0

noncomputable def ons_decMiddleBalancedRowWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) (lambda : ℂ)
    (site : ZMod L × ZMod L) : ons_Dart L ⊕ Fin 2 → ℂ
  | .inl _ => 1
  | .inr _ => lambda⁻¹ * decWeight (ons_decChainEdge site 1)

noncomputable def ons_decMiddleBalancedColWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) (t lambda : ℂ) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => decWeight s(d, ons_dartRev L d)
  | .inr _ => t * lambda

end StatMech.Onsager
