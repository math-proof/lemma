/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/IntegrandLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint
import Theorem.StatisticalMechanics.Code.Onsager.FreeEnergy
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
import Theorem.StatisticalMechanics.Code.Onsager.SymbolDet
import Theorem.StatisticalMechanics.Code.Onsager.IntegrandLimit
open scoped Real
open MeasureTheory


namespace StatMech.Onsager

noncomputable def ons_symbolDispersion (β k₁ k₂ : ℝ) : ℝ :=
  (1 + Real.tanh β ^ 2) ^ 2 -
    2 * Real.tanh β * (1 - Real.tanh β ^ 2) * (Real.cos k₁ + Real.cos k₂)

end StatMech.Onsager
