module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part4


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

noncomputable def ons_mvSeriesEval
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) : ℂ :=
  ∑' m : E →₀ ℕ,
    MvPowerSeries.coeff m series *
      m.prod (fun edge n ↦ weight edge ^ n)

end StatMech.Onsager
