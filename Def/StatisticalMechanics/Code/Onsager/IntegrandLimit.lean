module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint
public import Theorem.StatisticalMechanics.Code.Onsager.FreeEnergy
public import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
public import Theorem.StatisticalMechanics.Code.Onsager.SymbolDet
public import Theorem.StatisticalMechanics.Code.Onsager.IntegrandLimit
open scoped Real
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

noncomputable def ons_symbolDispersion (β k₁ k₂ : ℝ) : ℝ :=
  (1 + Real.tanh β ^ 2) ^ 2 -
    2 * Real.tanh β * (1 - Real.tanh β ^ 2) * (Real.cos k₁ + Real.cos k₂)

end StatMech.Onsager
