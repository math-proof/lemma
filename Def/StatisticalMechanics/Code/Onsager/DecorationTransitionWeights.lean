/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly.Part3


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


def ons_decChainEdge {L : ℕ}
    (site : ZMod L × ZMod L) (i : Fin 3) : Sym2 (ons_Dart L) :=
  s((site, ⟨i.val, by omega⟩), (site, ⟨i.val + 1, by omega⟩))


def ons_decChainPathIndices (a b : Fin 4) : Finset (Fin 3) :=
  Finset.univ.filter fun i ↦ (i.val < a.val) ≠ (i.val < b.val)

def ons_decChainPathEdges {L : ℕ}
    (site : ZMod L × ZMod L) (a b : Fin 4) :
    Finset (Sym2 (ons_Dart L)) :=
  (ons_decChainPathIndices a b).image (ons_decChainEdge site)


def ons_decTransitionWeight
    (L : ℕ) (decWeight : Sym2 (ons_Dart L) → ℂ)
    (d₂ d₁ : ons_Dart L) : ℂ :=
  decWeight s(d₁, ons_dartRev L d₁) *
    ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
      decWeight (ons_decChainEdge d₂.1 i)


noncomputable def ons_KWmatDecorationWeightedPhase
    (L : ℕ) (decWeight : Sym2 (ons_Dart L) → ℂ)
    (omega u v : ℂ) : Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d₂ d₁ ↦
    if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
      ons_dirPhase u v d₁.2 *
        (ons_decTransitionWeight L decWeight d₂ d₁ *
          ons_turnW omega d₁.2 d₂.2)
    else 0

noncomputable def ons_decSpecializedWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ons_Dart L)) : ℂ := by
  classical
  exact if ons_decIsExternal edge then
      weight (ons_decEdgeProjection edge)
    else 1

noncomputable def ons_decInterpolatedWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ) (t : ℂ)
    (edge : Sym2 (ons_Dart L)) : ℂ := by
  classical
  exact if ons_decIsExternal edge then
      weight (ons_decEdgeProjection edge)
    else t

end StatMech.Onsager
