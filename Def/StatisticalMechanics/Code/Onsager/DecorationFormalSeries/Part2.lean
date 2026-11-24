module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalLogCoeff
    (L : ℕ) [NeZero L] (omega u v : ℂ)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
      (∑ d : Fin (r + 1) → ons_Dart L,
        if ons_decLoopExponent L d = m then
          ons_decLoopScalar L omega u v d
        else 0) / ((r : ℂ) + 1)) / 2

noncomputable def ons_decFormalLog
    (L : ℕ) [NeZero L] (omega u v : ℂ) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalLogCoeff L omega u v

end StatMech.Onsager
