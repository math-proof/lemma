/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Abbrev.StatisticalMechanics.Code.Onsager.DecorationFormalSeries


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decTransitionExponent
    (L : ℕ) (d₂ d₁ : ons_Dart L) : ons_DecEdge L →₀ ℕ := by
  classical
  exact Finsupp.single s(d₁, ons_dartRev L d₁) 1 +
    ∑ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
      Finsupp.single (ons_decChainEdge d₂.1 i) 1

noncomputable def ons_decTransitionScalar
    (L : ℕ) (omega u v : ℂ) (d₂ d₁ : ons_Dart L) : ℂ :=
  if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
    ons_dirPhase u v d₁.2 * ons_turnW omega d₁.2 d₂.2
  else 0

noncomputable def ons_decFormalTransition
    (L : ℕ) (omega u v : ℂ) (d₂ d₁ : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  MvPowerSeries.monomial (ons_decTransitionExponent L d₂ d₁)
    (ons_decTransitionScalar L omega u v d₂ d₁)

noncomputable def ons_decLoopExponent
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_DecEdge L →₀ ℕ :=
  ∑ k, ons_decTransitionExponent L (d k) (d (k + 1))

noncomputable def ons_decLoopScalar
    (L : ℕ) (omega u v : ℂ) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L) : ℂ :=
  ∏ k, ons_decTransitionScalar L omega u v (d k) (d (k + 1))

def ons_finsuppTotalDegree {E : Type*} (m : E →₀ ℕ) : ℕ :=
  m.sum fun _ n ↦ n

end StatMech.Onsager
