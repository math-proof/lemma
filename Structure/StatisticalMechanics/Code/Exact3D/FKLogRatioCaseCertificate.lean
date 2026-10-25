/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


structure EpsilonTable
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (Case : Type*) [DecidableEq Case]
    (epsilon : ℝ) where
  table : RatInterval.CaseTable Case
  classify : ℝ → Case
  window : ℝ
  window_pos : 0 < window
  covers_on_Ioo :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
      classify p ∈ table.cases
  sound_on_Ioo :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
      (table.interval (classify p)).MemR (logRatioValue fkMass p)
  lower_inside_slack :
    ∀ k, k ∈ table.cases →
      C.predictedExponent - epsilon < ((table.interval k).lower : ℝ)
  upper_inside_slack :
    ∀ k, k ∈ table.cases →
      ((table.interval k).upper : ℝ) < C.predictedExponent + epsilon

set_option linter.style.longLine false in


structure Certificate
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (Case : Type*) [DecidableEq Case] where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  epsilonTable :
    ∀ epsilon, 0 < epsilon → EpsilonTable C fkMass Case epsilon

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
