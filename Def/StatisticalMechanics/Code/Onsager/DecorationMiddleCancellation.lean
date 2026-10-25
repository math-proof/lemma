/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part5


namespace StatMech.Onsager

open Matrix BigOperators

def ons_decMiddleAugRev (L : ℕ) :
    ons_Dart L ⊕ Fin 2 → ons_Dart L ⊕ Fin 2
  | .inl d => .inl (ons_dartRev L d)
  | .inr side => .inr (side + 1)

def ons_decMiddleAugDir {L : ℕ} :
    ons_Dart L ⊕ Fin 2 → Fin 4
  | .inl d => d.2
  | .inr side => ons_decMiddleDir side

noncomputable def ons_decMiddleRowWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (t : ℂ) (site : ZMod L × ZMod L) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl _ => 1
  | .inr _ => t * decWeight (ons_decChainEdge site 1)

noncomputable def ons_decMiddleColWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => decWeight s(d, ons_dartRev L d)
  | .inr _ => 1


noncomputable def ons_decMiddleInternalFactor
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (site : ZMod L × ZMod L) :
    (ons_Dart L ⊕ Fin 2) → (ons_Dart L ⊕ Fin 2) → ℂ
  | .inl d₂, .inl d₁ =>
      if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
        ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
          ons_scaleDecEdgeWeight decWeight
            (ons_decChainEdge site 1) 0 (ons_decChainEdge d₂.1 i)
      else 0
  | .inl d₂, .inr side =>
      if d₂.1 = site ∧ ons_decMiddleSide d₂.2 = side then
        ons_decMiddleDestFactor decWeight site d₂.2
      else 0
  | .inr side, .inl d₁ =>
      if site = ons_dirStep L d₁.2 d₁.1 ∧
          ons_decMiddleSide d₁.2 = side then
        ons_decMiddleSourceFactor decWeight site d₁.2
      else 0
  | .inr _, .inr _ => 0

end StatMech.Onsager
